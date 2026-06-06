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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_checkInvariants(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_ppState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_preprocessLight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Grind_PendingSolverPropagations_propagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_DelayedTheoremInstance_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
uint64_t l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 64, 101, 181, 200, 140, 42, 219)}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "curr: "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object* v_parent_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_parent_155_);
lean_dec_ref(v_parent_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(lean_object* v_msgData_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; lean_object* v_env_165_; lean_object* v___x_166_; lean_object* v_mctx_167_; lean_object* v_lctx_168_; lean_object* v_options_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_164_ = lean_st_ref_get(v___y_162_);
v_env_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc_ref(v_env_165_);
lean_dec(v___x_164_);
v___x_166_ = lean_st_ref_get(v___y_160_);
v_mctx_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc_ref(v_mctx_167_);
lean_dec(v___x_166_);
v_lctx_168_ = lean_ctor_get(v___y_159_, 2);
v_options_169_ = lean_ctor_get(v___y_161_, 2);
lean_inc_ref(v_options_169_);
lean_inc_ref(v_lctx_168_);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v_env_165_);
lean_ctor_set(v___x_170_, 1, v_mctx_167_);
lean_ctor_set(v___x_170_, 2, v_lctx_168_);
lean_ctor_set(v___x_170_, 3, v_options_169_);
v___x_171_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_msgData_158_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2___boxed(lean_object* v_msgData_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msgData_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_179_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_180_; double v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = lean_float_of_nat(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object* v_cls_185_, lean_object* v_msg_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_ref_192_; lean_object* v___x_193_; lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_238_; 
v_ref_192_ = lean_ctor_get(v___y_189_, 5);
v___x_193_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msg_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_238_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_238_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_238_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v_traceState_199_; lean_object* v_env_200_; lean_object* v_nextMacroScope_201_; lean_object* v_ngen_202_; lean_object* v_auxDeclNGen_203_; lean_object* v_cache_204_; lean_object* v_messages_205_; lean_object* v_infoState_206_; lean_object* v_snapshotTasks_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_237_; 
v___x_198_ = lean_st_ref_take(v___y_190_);
v_traceState_199_ = lean_ctor_get(v___x_198_, 4);
v_env_200_ = lean_ctor_get(v___x_198_, 0);
v_nextMacroScope_201_ = lean_ctor_get(v___x_198_, 1);
v_ngen_202_ = lean_ctor_get(v___x_198_, 2);
v_auxDeclNGen_203_ = lean_ctor_get(v___x_198_, 3);
v_cache_204_ = lean_ctor_get(v___x_198_, 5);
v_messages_205_ = lean_ctor_get(v___x_198_, 6);
v_infoState_206_ = lean_ctor_get(v___x_198_, 7);
v_snapshotTasks_207_ = lean_ctor_get(v___x_198_, 8);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_237_ == 0)
{
v___x_209_ = v___x_198_;
v_isShared_210_ = v_isSharedCheck_237_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_snapshotTasks_207_);
lean_inc(v_infoState_206_);
lean_inc(v_messages_205_);
lean_inc(v_cache_204_);
lean_inc(v_traceState_199_);
lean_inc(v_auxDeclNGen_203_);
lean_inc(v_ngen_202_);
lean_inc(v_nextMacroScope_201_);
lean_inc(v_env_200_);
lean_dec(v___x_198_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_237_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
uint64_t v_tid_211_; lean_object* v_traces_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_236_; 
v_tid_211_ = lean_ctor_get_uint64(v_traceState_199_, sizeof(void*)*1);
v_traces_212_ = lean_ctor_get(v_traceState_199_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v_traceState_199_);
if (v_isSharedCheck_236_ == 0)
{
v___x_214_ = v_traceState_199_;
v_isShared_215_ = v_isSharedCheck_236_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_traces_212_);
lean_dec(v_traceState_199_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_236_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; double v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_216_ = lean_box(0);
v___x_217_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0);
v___x_218_ = 0;
v___x_219_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
v___x_220_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_220_, 0, v_cls_185_);
lean_ctor_set(v___x_220_, 1, v___x_216_);
lean_ctor_set(v___x_220_, 2, v___x_219_);
lean_ctor_set_float(v___x_220_, sizeof(void*)*3, v___x_217_);
lean_ctor_set_float(v___x_220_, sizeof(void*)*3 + 8, v___x_217_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*3 + 16, v___x_218_);
v___x_221_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2));
v___x_222_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v_a_194_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
lean_inc(v_ref_192_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v_ref_192_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = l_Lean_PersistentArray_push___redArg(v_traces_212_, v___x_223_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_224_);
v___x_226_ = v___x_214_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_224_);
lean_ctor_set_uint64(v_reuseFailAlloc_235_, sizeof(void*)*1, v_tid_211_);
v___x_226_ = v_reuseFailAlloc_235_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_228_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 4, v___x_226_);
v___x_228_ = v___x_209_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_env_200_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_nextMacroScope_201_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_ngen_202_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_auxDeclNGen_203_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_234_, 5, v_cache_204_);
lean_ctor_set(v_reuseFailAlloc_234_, 6, v_messages_205_);
lean_ctor_set(v_reuseFailAlloc_234_, 7, v_infoState_206_);
lean_ctor_set(v_reuseFailAlloc_234_, 8, v_snapshotTasks_207_);
v___x_228_ = v_reuseFailAlloc_234_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_229_ = lean_st_ref_set(v___y_190_, v___x_228_);
v___x_230_ = lean_box(0);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_230_);
v___x_232_ = v___x_196_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object* v_cls_239_, lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_239_, v_msg_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(lean_object* v___x_247_, lean_object* v_xs_248_, lean_object* v_v_249_, lean_object* v_i_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_array_get_size(v_xs_248_);
v___x_252_ = lean_nat_dec_lt(v_i_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v_i_250_);
lean_dec_ref(v_v_249_);
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_array_fget_borrowed(v_xs_248_, v_i_250_);
lean_inc_ref(v_v_249_);
lean_inc(v___x_254_);
v___x_255_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_247_, v___x_254_, v_v_249_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_i_250_, v___x_256_);
lean_dec(v_i_250_);
v_i_250_ = v___x_257_;
goto _start;
}
else
{
lean_object* v___x_259_; 
lean_dec_ref(v_v_249_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v_i_250_);
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v___x_260_, lean_object* v_xs_261_, lean_object* v_v_262_, lean_object* v_i_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_260_, v_xs_261_, v_v_262_, v_i_263_);
lean_dec_ref(v_xs_261_);
lean_dec_ref(v___x_260_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(lean_object* v___x_265_, lean_object* v_xs_266_, lean_object* v_v_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_265_, v_xs_266_, v_v_267_, v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1___boxed(lean_object* v___x_270_, lean_object* v_xs_271_, lean_object* v_v_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_270_, v_xs_271_, v_v_272_);
lean_dec_ref(v_xs_271_);
lean_dec_ref(v___x_270_);
return v_res_273_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; 
v___x_274_ = ((size_t)5ULL);
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_shift_left(v___x_275_, v___x_274_);
return v___x_276_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_277_; size_t v___x_278_; size_t v___x_279_; 
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0);
v___x_279_ = lean_usize_sub(v___x_278_, v___x_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* v___x_280_, lean_object* v_x_281_, size_t v_x_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
lean_object* v_es_284_; lean_object* v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; lean_object* v_j_289_; lean_object* v_entry_290_; 
v_es_284_ = lean_ctor_get(v_x_281_, 0);
v___x_285_ = lean_box(2);
v___x_286_ = ((size_t)5ULL);
v___x_287_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_288_ = lean_usize_land(v_x_282_, v___x_287_);
v_j_289_ = lean_usize_to_nat(v___x_288_);
v_entry_290_ = lean_array_get(v___x_285_, v_es_284_, v_j_289_);
switch(lean_obj_tag(v_entry_290_))
{
case 0:
{
lean_object* v_key_291_; uint8_t v___x_292_; 
v_key_291_ = lean_ctor_get(v_entry_290_, 0);
lean_inc(v_key_291_);
lean_dec_ref_known(v_entry_290_, 2);
v___x_292_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_280_, v_x_283_, v_key_291_);
if (v___x_292_ == 0)
{
lean_dec(v_j_289_);
return v_x_281_;
}
else
{
lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_300_; 
lean_inc_ref(v_es_284_);
v_isSharedCheck_300_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v_x_281_, 0);
lean_dec(v_unused_301_);
v___x_294_ = v_x_281_;
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
else
{
lean_dec(v_x_281_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_array_set(v_es_284_, v_j_289_, v___x_285_);
lean_dec(v_j_289_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_296_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
case 1:
{
lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_335_; 
lean_inc_ref(v_es_284_);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v_x_281_, 0);
lean_dec(v_unused_336_);
v___x_303_ = v_x_281_;
v_isShared_304_ = v_isSharedCheck_335_;
goto v_resetjp_302_;
}
else
{
lean_dec(v_x_281_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_335_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v_node_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_334_; 
v_node_305_ = lean_ctor_get(v_entry_290_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_entry_290_);
if (v_isSharedCheck_334_ == 0)
{
v___x_307_ = v_entry_290_;
v_isShared_308_ = v_isSharedCheck_334_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_node_305_);
lean_dec(v_entry_290_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_334_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_entries_309_; size_t v___x_310_; lean_object* v_newNode_311_; lean_object* v___x_312_; 
v_entries_309_ = lean_array_set(v_es_284_, v_j_289_, v___x_285_);
v___x_310_ = lean_usize_shift_right(v_x_282_, v___x_286_);
v_newNode_311_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_280_, v_node_305_, v___x_310_, v_x_283_);
lean_inc_ref(v_newNode_311_);
v___x_312_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_314_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v_newNode_311_);
v___x_314_ = v___x_307_;
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
v___x_315_ = lean_array_set(v_entries_309_, v_j_289_, v___x_314_);
lean_dec(v_j_289_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_315_);
v___x_317_ = v___x_303_;
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
lean_del_object(v___x_307_);
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
v___x_328_ = lean_array_set(v_entries_309_, v_j_289_, v___x_327_);
lean_dec(v_j_289_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_328_);
v___x_330_ = v___x_303_;
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
lean_dec(v_j_289_);
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
size_t v_x_28249__boxed_357_; lean_object* v_res_358_; 
v_x_28249__boxed_357_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_358_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_353_, v_x_354_, v_x_28249__boxed_357_, v_x_356_);
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
lean_object* v_head_399_; lean_object* v_tail_400_; lean_object* v___x_401_; lean_object* v___y_403_; uint8_t v_a_443_; uint8_t v___x_456_; 
v_head_399_ = lean_ctor_get(v_as_x27_385_, 0);
v_tail_400_ = lean_ctor_get(v_as_x27_385_, 1);
v___x_401_ = lean_box(0);
v___x_456_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_399_);
if (v___x_456_ == 0)
{
v_a_443_ = v___x_456_;
goto v___jp_442_;
}
else
{
lean_object* v___x_457_; 
lean_inc(v_head_399_);
v___x_457_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_399_, v___y_387_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; uint8_t v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v___x_459_ = lean_unbox(v_a_458_);
lean_dec(v_a_458_);
v_a_443_ = v___x_459_;
goto v___jp_442_;
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
v_a_460_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_457_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_457_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v_toGoalState_405_; lean_object* v_mvarId_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_441_; 
v___x_404_ = lean_st_ref_take(v___y_403_);
v_toGoalState_405_ = lean_ctor_get(v___x_404_, 0);
v_mvarId_406_ = lean_ctor_get(v___x_404_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_441_ == 0)
{
v___x_408_ = v___x_404_;
v_isShared_409_ = v_isSharedCheck_441_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_mvarId_406_);
lean_inc(v_toGoalState_405_);
lean_dec(v___x_404_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_441_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_nextDeclIdx_410_; lean_object* v_enodeMap_411_; lean_object* v_exprs_412_; lean_object* v_parents_413_; lean_object* v_congrTable_414_; lean_object* v_appMap_415_; lean_object* v_indicesFound_416_; lean_object* v_newFacts_417_; uint8_t v_inconsistent_418_; lean_object* v_nextIdx_419_; lean_object* v_newRawFacts_420_; lean_object* v_facts_421_; lean_object* v_extThms_422_; lean_object* v_ematch_423_; lean_object* v_inj_424_; lean_object* v_split_425_; lean_object* v_clean_426_; lean_object* v_sstates_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_440_; 
v_nextDeclIdx_410_ = lean_ctor_get(v_toGoalState_405_, 0);
v_enodeMap_411_ = lean_ctor_get(v_toGoalState_405_, 1);
v_exprs_412_ = lean_ctor_get(v_toGoalState_405_, 2);
v_parents_413_ = lean_ctor_get(v_toGoalState_405_, 3);
v_congrTable_414_ = lean_ctor_get(v_toGoalState_405_, 4);
v_appMap_415_ = lean_ctor_get(v_toGoalState_405_, 5);
v_indicesFound_416_ = lean_ctor_get(v_toGoalState_405_, 6);
v_newFacts_417_ = lean_ctor_get(v_toGoalState_405_, 7);
v_inconsistent_418_ = lean_ctor_get_uint8(v_toGoalState_405_, sizeof(void*)*17);
v_nextIdx_419_ = lean_ctor_get(v_toGoalState_405_, 8);
v_newRawFacts_420_ = lean_ctor_get(v_toGoalState_405_, 9);
v_facts_421_ = lean_ctor_get(v_toGoalState_405_, 10);
v_extThms_422_ = lean_ctor_get(v_toGoalState_405_, 11);
v_ematch_423_ = lean_ctor_get(v_toGoalState_405_, 12);
v_inj_424_ = lean_ctor_get(v_toGoalState_405_, 13);
v_split_425_ = lean_ctor_get(v_toGoalState_405_, 14);
v_clean_426_ = lean_ctor_get(v_toGoalState_405_, 15);
v_sstates_427_ = lean_ctor_get(v_toGoalState_405_, 16);
v_isSharedCheck_440_ = !lean_is_exclusive(v_toGoalState_405_);
if (v_isSharedCheck_440_ == 0)
{
v___x_429_ = v_toGoalState_405_;
v_isShared_430_ = v_isSharedCheck_440_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_sstates_427_);
lean_inc(v_clean_426_);
lean_inc(v_split_425_);
lean_inc(v_inj_424_);
lean_inc(v_ematch_423_);
lean_inc(v_extThms_422_);
lean_inc(v_facts_421_);
lean_inc(v_newRawFacts_420_);
lean_inc(v_nextIdx_419_);
lean_inc(v_newFacts_417_);
lean_inc(v_indicesFound_416_);
lean_inc(v_appMap_415_);
lean_inc(v_congrTable_414_);
lean_inc(v_parents_413_);
lean_inc(v_exprs_412_);
lean_inc(v_enodeMap_411_);
lean_inc(v_nextDeclIdx_410_);
lean_dec(v_toGoalState_405_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_440_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
lean_inc(v_head_399_);
v___x_431_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_411_, v_congrTable_414_, v_head_399_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 4, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_nextDeclIdx_410_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_enodeMap_411_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_exprs_412_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_parents_413_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_439_, 5, v_appMap_415_);
lean_ctor_set(v_reuseFailAlloc_439_, 6, v_indicesFound_416_);
lean_ctor_set(v_reuseFailAlloc_439_, 7, v_newFacts_417_);
lean_ctor_set(v_reuseFailAlloc_439_, 8, v_nextIdx_419_);
lean_ctor_set(v_reuseFailAlloc_439_, 9, v_newRawFacts_420_);
lean_ctor_set(v_reuseFailAlloc_439_, 10, v_facts_421_);
lean_ctor_set(v_reuseFailAlloc_439_, 11, v_extThms_422_);
lean_ctor_set(v_reuseFailAlloc_439_, 12, v_ematch_423_);
lean_ctor_set(v_reuseFailAlloc_439_, 13, v_inj_424_);
lean_ctor_set(v_reuseFailAlloc_439_, 14, v_split_425_);
lean_ctor_set(v_reuseFailAlloc_439_, 15, v_clean_426_);
lean_ctor_set(v_reuseFailAlloc_439_, 16, v_sstates_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_439_, sizeof(void*)*17, v_inconsistent_418_);
v___x_433_ = v_reuseFailAlloc_439_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_433_);
v___x_435_ = v___x_408_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_mvarId_406_);
v___x_435_ = v_reuseFailAlloc_438_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; 
v___x_436_ = lean_st_ref_set(v___y_403_, v___x_435_);
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
}
}
}
}
v___jp_442_:
{
if (v_a_443_ == 0)
{
v_as_x27_385_ = v_tail_400_;
v_b_386_ = v___x_401_;
goto _start;
}
else
{
lean_object* v_options_445_; uint8_t v_hasTrace_446_; 
v_options_445_ = lean_ctor_get(v___y_395_, 2);
v_hasTrace_446_ = lean_ctor_get_uint8(v_options_445_, sizeof(void*)*1);
if (v_hasTrace_446_ == 0)
{
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
lean_object* v_inheritedTraceOptions_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_inheritedTraceOptions_447_ = lean_ctor_get(v___y_395_, 13);
v___x_448_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_449_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_450_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_447_, v_options_445_, v___x_449_);
if (v___x_450_ == 0)
{
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Grind_updateLastTag(v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec_ref_known(v___x_451_, 1);
v___x_452_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_399_);
v___x_453_ = l_Lean_MessageData_ofExpr(v_head_399_);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_448_, v___x_454_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_dec_ref_known(v___x_455_, 1);
v___y_403_ = v___y_387_;
goto v___jp_402_;
}
else
{
return v___x_455_;
}
}
else
{
return v___x_451_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_468_, lean_object* v_b_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_468_, v_b_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec(v___y_470_);
lean_dec(v_as_x27_468_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Meta_Grind_getParents___redArg(v_root_482_, v_a_483_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref_known(v___x_494_, 1);
v___x_496_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_495_);
v___x_497_ = lean_box(0);
v___x_498_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_496_, v___x_497_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_);
lean_dec(v___x_496_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v___x_498_, 0);
lean_dec(v_unused_506_);
v___x_500_ = v___x_498_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_dec(v___x_498_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v_a_495_);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_495_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec(v_a_495_);
v_a_507_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_498_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_498_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
else
{
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_a_524_);
lean_dec(v_a_523_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_root_515_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_528_, lean_object* v_00_u03b2_529_, lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_528_, v_x_530_, v_x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_533_, lean_object* v_00_u03b2_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_533_, v_00_u03b2_534_, v_x_535_, v_x_536_);
lean_dec_ref(v___x_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_538_, lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_538_, v_msg_539_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_552_, lean_object* v_msg_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_552_, v_msg_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec(v___y_554_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_566_, lean_object* v_as_x27_567_, lean_object* v_b_568_, lean_object* v_a_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_567_, v_b_568_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_582_, lean_object* v_as_x27_583_, lean_object* v_b_584_, lean_object* v_a_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_582_, v_as_x27_583_, v_b_584_, v_a_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec(v___y_586_);
lean_dec(v_as_x27_583_);
lean_dec(v_as_582_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_598_, lean_object* v_00_u03b2_599_, lean_object* v_x_600_, size_t v_x_601_, lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_598_, v_x_600_, v_x_601_, v_x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_604_, lean_object* v_00_u03b2_605_, lean_object* v_x_606_, lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
size_t v_x_28717__boxed_609_; lean_object* v_res_610_; 
v_x_28717__boxed_609_ = lean_unbox_usize(v_x_607_);
lean_dec(v_x_607_);
v_res_610_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_604_, v_00_u03b2_605_, v_x_606_, v_x_28717__boxed_609_, v_x_608_);
lean_dec_ref(v___x_604_);
return v_res_610_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_613_ = l_Lean_stringToMessageData(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_614_, lean_object* v_b_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
if (lean_obj_tag(v_as_x27_614_) == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_b_615_);
return v___x_627_;
}
else
{
lean_object* v_head_628_; lean_object* v_tail_629_; lean_object* v___x_630_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; uint8_t v_a_645_; uint8_t v___x_658_; 
v_head_628_ = lean_ctor_get(v_as_x27_614_, 0);
v_tail_629_ = lean_ctor_get(v_as_x27_614_, 1);
v___x_630_ = lean_box(0);
v___x_658_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_628_);
if (v___x_658_ == 0)
{
v_a_645_ = v___x_658_;
goto v___jp_644_;
}
else
{
lean_object* v___x_659_; 
lean_inc(v_head_628_);
v___x_659_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_628_, v___y_616_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; uint8_t v___x_661_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
v___x_661_ = lean_unbox(v_a_660_);
lean_dec(v_a_660_);
v_a_645_ = v___x_661_;
goto v___jp_644_;
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_659_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_659_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
v___jp_631_:
{
lean_object* v___x_642_; 
lean_inc(v_head_628_);
v___x_642_ = l_Lean_Meta_Grind_addCongrTable(v_head_628_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_dec_ref_known(v___x_642_, 1);
v_as_x27_614_ = v_tail_629_;
v_b_615_ = v___x_630_;
goto _start;
}
else
{
return v___x_642_;
}
}
v___jp_644_:
{
if (v_a_645_ == 0)
{
v_as_x27_614_ = v_tail_629_;
v_b_615_ = v___x_630_;
goto _start;
}
else
{
lean_object* v_options_647_; uint8_t v_hasTrace_648_; 
v_options_647_ = lean_ctor_get(v___y_624_, 2);
v_hasTrace_648_ = lean_ctor_get_uint8(v_options_647_, sizeof(void*)*1);
if (v_hasTrace_648_ == 0)
{
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
goto v___jp_631_;
}
else
{
lean_object* v_inheritedTraceOptions_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_inheritedTraceOptions_649_ = lean_ctor_get(v___y_624_, 13);
v___x_650_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_651_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_652_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_649_, v_options_647_, v___x_651_);
if (v___x_652_ == 0)
{
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
goto v___jp_631_;
}
else
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_Grind_updateLastTag(v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec_ref_known(v___x_653_, 1);
v___x_654_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_628_);
v___x_655_ = l_Lean_MessageData_ofExpr(v_head_628_);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_650_, v___x_656_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref_known(v___x_657_, 1);
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
v___y_641_ = v___y_625_;
goto v___jp_631_;
}
else
{
return v___x_657_;
}
}
else
{
return v___x_653_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_670_, lean_object* v_b_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_670_, v_b_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
lean_dec(v_as_x27_670_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_684_);
v___x_697_ = lean_box(0);
v___x_698_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_696_, v___x_697_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v___x_696_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v___x_698_, 0);
lean_dec(v_unused_706_);
v___x_700_ = v___x_698_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_dec(v___x_698_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_697_);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_697_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec(v_a_708_);
lean_dec(v_parents_707_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_720_, lean_object* v_as_x27_721_, lean_object* v_b_722_, lean_object* v_a_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_721_, v_b_722_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_736_, lean_object* v_as_x27_737_, lean_object* v_b_738_, lean_object* v_a_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_736_, v_as_x27_737_, v_b_738_, v_a_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec(v___y_740_);
lean_dec(v_as_x27_737_);
lean_dec(v_as_736_);
return v_res_751_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_752_, lean_object* v_i_753_, lean_object* v_k_754_){
_start:
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = lean_array_get_size(v_keys_752_);
v___x_756_ = lean_nat_dec_lt(v_i_753_, v___x_755_);
if (v___x_756_ == 0)
{
lean_dec(v_i_753_);
return v___x_756_;
}
else
{
lean_object* v_k_x27_757_; uint8_t v___x_758_; 
v_k_x27_757_ = lean_array_fget_borrowed(v_keys_752_, v_i_753_);
v___x_758_ = l_Lean_instBEqMVarId_beq(v_k_754_, v_k_x27_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_nat_add(v_i_753_, v___x_759_);
lean_dec(v_i_753_);
v_i_753_ = v___x_760_;
goto _start;
}
else
{
lean_dec(v_i_753_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_762_, lean_object* v_i_763_, lean_object* v_k_764_){
_start:
{
uint8_t v_res_765_; lean_object* v_r_766_; 
v_res_765_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_762_, v_i_763_, v_k_764_);
lean_dec(v_k_764_);
lean_dec_ref(v_keys_762_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_767_, size_t v_x_768_, lean_object* v_x_769_){
_start:
{
if (lean_obj_tag(v_x_767_) == 0)
{
lean_object* v_es_770_; lean_object* v___x_771_; size_t v___x_772_; size_t v___x_773_; size_t v___x_774_; lean_object* v_j_775_; lean_object* v___x_776_; 
v_es_770_ = lean_ctor_get(v_x_767_, 0);
v___x_771_ = lean_box(2);
v___x_772_ = ((size_t)5ULL);
v___x_773_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_774_ = lean_usize_land(v_x_768_, v___x_773_);
v_j_775_ = lean_usize_to_nat(v___x_774_);
v___x_776_ = lean_array_get_borrowed(v___x_771_, v_es_770_, v_j_775_);
lean_dec(v_j_775_);
switch(lean_obj_tag(v___x_776_))
{
case 0:
{
lean_object* v_key_777_; uint8_t v___x_778_; 
v_key_777_ = lean_ctor_get(v___x_776_, 0);
v___x_778_ = l_Lean_instBEqMVarId_beq(v_x_769_, v_key_777_);
return v___x_778_;
}
case 1:
{
lean_object* v_node_779_; size_t v___x_780_; 
v_node_779_ = lean_ctor_get(v___x_776_, 0);
v___x_780_ = lean_usize_shift_right(v_x_768_, v___x_772_);
v_x_767_ = v_node_779_;
v_x_768_ = v___x_780_;
goto _start;
}
default: 
{
uint8_t v___x_782_; 
v___x_782_ = 0;
return v___x_782_;
}
}
}
else
{
lean_object* v_ks_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_ks_783_ = lean_ctor_get(v_x_767_, 0);
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_783_, v___x_784_, v_x_769_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
size_t v_x_10242__boxed_789_; uint8_t v_res_790_; lean_object* v_r_791_; 
v_x_10242__boxed_789_ = lean_unbox_usize(v_x_787_);
lean_dec(v_x_787_);
v_res_790_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_786_, v_x_10242__boxed_789_, v_x_788_);
lean_dec(v_x_788_);
lean_dec_ref(v_x_786_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
uint64_t v___x_794_; size_t v___x_795_; uint8_t v___x_796_; 
v___x_794_ = l_Lean_instHashableMVarId_hash(v_x_793_);
v___x_795_ = lean_uint64_to_usize(v___x_794_);
v___x_796_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_792_, v___x_795_, v_x_793_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_797_, v_x_798_);
lean_dec(v_x_798_);
lean_dec_ref(v_x_797_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; lean_object* v_mctx_805_; lean_object* v_eAssignment_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_804_ = lean_st_ref_get(v___y_802_);
v_mctx_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc_ref(v_mctx_805_);
lean_dec(v___x_804_);
v_eAssignment_806_ = lean_ctor_get(v_mctx_805_, 8);
lean_inc_ref(v_eAssignment_806_);
lean_dec_ref(v_mctx_805_);
v___x_807_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_806_, v_mvarId_801_);
lean_dec_ref(v_eAssignment_806_);
v___x_808_ = lean_box(v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec(v_mvarId_810_);
return v_res_813_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_824_ = l_Lean_mkConst(v___x_823_, v___x_822_);
return v___x_824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = lean_box(0);
v___x_831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_832_ = l_Lean_mkConst(v___x_831_, v___x_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_844_; lean_object* v_mvarId_845_; lean_object* v___x_846_; lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_900_; 
v___x_844_ = lean_st_ref_get(v_a_833_);
v_mvarId_845_ = lean_ctor_get(v___x_844_, 1);
lean_inc(v_mvarId_845_);
lean_dec(v___x_844_);
v___x_846_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_845_, v_a_840_);
lean_dec(v_mvarId_845_);
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_900_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_900_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_900_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
uint8_t v___x_851_; 
v___x_851_ = lean_unbox(v_a_847_);
lean_dec(v_a_847_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; 
lean_del_object(v___x_849_);
v___x_852_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_837_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_853_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_837_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_837_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_862_ = l_Lean_mkApp4(v___x_860_, v_a_857_, v_a_859_, v_a_855_, v___x_861_);
v___x_863_ = l_Lean_Meta_Grind_closeGoal(v___x_862_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
return v___x_863_;
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v_a_857_);
lean_dec(v_a_855_);
v_a_864_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_858_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_858_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_855_);
v_a_872_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_856_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_856_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
v_a_880_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_854_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_854_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_852_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_852_);
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
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_box(0);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_896_);
v___x_898_ = v___x_849_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec(v_a_901_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_913_, v___y_921_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec(v___y_927_);
lean_dec(v_mvarId_926_);
return v_res_938_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_940_, v_x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
uint8_t v_res_946_; lean_object* v_r_947_; 
v_res_946_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_943_, v_x_944_, v_x_945_);
lean_dec(v_x_945_);
lean_dec_ref(v_x_944_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_948_, lean_object* v_x_949_, size_t v_x_950_, lean_object* v_x_951_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_949_, v_x_950_, v_x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_953_, lean_object* v_x_954_, lean_object* v_x_955_, lean_object* v_x_956_){
_start:
{
size_t v_x_10527__boxed_957_; uint8_t v_res_958_; lean_object* v_r_959_; 
v_x_10527__boxed_957_ = lean_unbox_usize(v_x_955_);
lean_dec(v_x_955_);
v_res_958_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_953_, v_x_954_, v_x_10527__boxed_957_, v_x_956_);
lean_dec(v_x_956_);
lean_dec_ref(v_x_954_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_960_, lean_object* v_keys_961_, lean_object* v_vals_962_, lean_object* v_heq_963_, lean_object* v_i_964_, lean_object* v_k_965_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_961_, v_i_964_, v_k_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_967_, lean_object* v_keys_968_, lean_object* v_vals_969_, lean_object* v_heq_970_, lean_object* v_i_971_, lean_object* v_k_972_){
_start:
{
uint8_t v_res_973_; lean_object* v_r_974_; 
v_res_973_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_967_, v_keys_968_, v_vals_969_, v_heq_970_, v_i_971_, v_k_972_);
lean_dec(v_k_972_);
lean_dec_ref(v_vals_969_);
lean_dec_ref(v_keys_968_);
v_r_974_ = lean_box(v_res_973_);
return v_r_974_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_box(0);
v___x_979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_980_ = l_Lean_mkConst(v___x_979_, v___x_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_981_, lean_object* v_rhs_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; 
lean_inc_ref(v_rhs_982_);
lean_inc_ref(v_lhs_981_);
v___x_994_ = l_Lean_Meta_mkEq(v_lhs_981_, v_rhs_982_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
lean_inc(v_a_992_);
lean_inc_ref(v_a_991_);
lean_inc(v_a_990_);
lean_inc_ref(v_a_989_);
lean_inc(v_a_988_);
lean_inc_ref(v_a_987_);
lean_inc(v_a_986_);
lean_inc_ref(v_a_985_);
lean_inc(v_a_984_);
lean_inc(v_a_983_);
v___x_996_ = lean_grind_mk_eq_proof(v_lhs_981_, v_rhs_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
lean_inc(v_a_995_);
v___x_998_ = l_Lean_Meta_mkDecide(v_a_995_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1000_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_987_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1003_ = l_Lean_Expr_appArg_x21(v_a_999_);
lean_dec(v_a_999_);
v___x_1004_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_995_);
v___x_1005_ = l_Lean_mkApp3(v___x_1002_, v_a_995_, v___x_1003_, v___x_1004_);
v___x_1006_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1007_ = l_Lean_mkApp4(v___x_1006_, v_a_995_, v_a_1001_, v___x_1005_, v_a_997_);
v___x_1008_ = l_Lean_Meta_Grind_closeGoal(v___x_1007_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_1008_;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec(v_a_999_);
lean_dec(v_a_997_);
lean_dec(v_a_995_);
v_a_1009_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1000_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1000_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v_a_997_);
lean_dec(v_a_995_);
v_a_1017_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_998_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_998_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_a_995_);
v_a_1025_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_996_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_996_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_rhs_982_);
lean_dec_ref(v_lhs_981_);
v_a_1033_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_994_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_994_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1041_, lean_object* v_rhs_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1041_, v_rhs_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec(v_a_1043_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1055_, lean_object* v_as_x27_1056_, lean_object* v_b_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
if (lean_obj_tag(v_as_x27_1056_) == 0)
{
lean_object* v___x_1069_; 
lean_dec(v___x_1055_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_b_1057_);
return v___x_1069_;
}
else
{
lean_object* v_head_1070_; lean_object* v_tail_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_head_1070_ = lean_ctor_get(v_as_x27_1056_, 0);
v_tail_1071_ = lean_ctor_get(v_as_x27_1056_, 1);
v___x_1072_ = lean_st_ref_get(v___y_1058_);
lean_inc(v_head_1070_);
v___x_1073_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1072_, v_head_1070_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___x_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v_self_1075_; lean_object* v_next_1076_; lean_object* v_root_1077_; lean_object* v_congr_1078_; lean_object* v_target_x3f_1079_; lean_object* v_proof_x3f_1080_; uint8_t v_flipped_1081_; lean_object* v_size_1082_; uint8_t v_interpreted_1083_; uint8_t v_ctor_1084_; uint8_t v_hasLambdas_1085_; uint8_t v_heqProofs_1086_; lean_object* v_idx_1087_; lean_object* v_generation_1088_; lean_object* v_mt_1089_; lean_object* v_sTerms_1090_; uint8_t v_funCC_1091_; lean_object* v_ematchDiagSource_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1105_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v_self_1075_ = lean_ctor_get(v_a_1074_, 0);
v_next_1076_ = lean_ctor_get(v_a_1074_, 1);
v_root_1077_ = lean_ctor_get(v_a_1074_, 2);
v_congr_1078_ = lean_ctor_get(v_a_1074_, 3);
v_target_x3f_1079_ = lean_ctor_get(v_a_1074_, 4);
v_proof_x3f_1080_ = lean_ctor_get(v_a_1074_, 5);
v_flipped_1081_ = lean_ctor_get_uint8(v_a_1074_, sizeof(void*)*12);
v_size_1082_ = lean_ctor_get(v_a_1074_, 6);
v_interpreted_1083_ = lean_ctor_get_uint8(v_a_1074_, sizeof(void*)*12 + 1);
v_ctor_1084_ = lean_ctor_get_uint8(v_a_1074_, sizeof(void*)*12 + 2);
v_hasLambdas_1085_ = lean_ctor_get_uint8(v_a_1074_, sizeof(void*)*12 + 3);
v_heqProofs_1086_ = lean_ctor_get_uint8(v_a_1074_, sizeof(void*)*12 + 4);
v_idx_1087_ = lean_ctor_get(v_a_1074_, 7);
v_generation_1088_ = lean_ctor_get(v_a_1074_, 8);
v_mt_1089_ = lean_ctor_get(v_a_1074_, 9);
v_sTerms_1090_ = lean_ctor_get(v_a_1074_, 10);
v_funCC_1091_ = lean_ctor_get_uint8(v_a_1074_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1092_ = lean_ctor_get(v_a_1074_, 11);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_a_1074_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1094_ = v_a_1074_;
v_isShared_1095_ = v_isSharedCheck_1105_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_ematchDiagSource_1092_);
lean_inc(v_sTerms_1090_);
lean_inc(v_mt_1089_);
lean_inc(v_generation_1088_);
lean_inc(v_idx_1087_);
lean_inc(v_size_1082_);
lean_inc(v_proof_x3f_1080_);
lean_inc(v_target_x3f_1079_);
lean_inc(v_congr_1078_);
lean_inc(v_root_1077_);
lean_inc(v_next_1076_);
lean_inc(v_self_1075_);
lean_dec(v_a_1074_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1105_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_nat_dec_lt(v_mt_1089_, v___x_1055_);
lean_dec(v_mt_1089_);
if (v___x_1097_ == 0)
{
lean_del_object(v___x_1094_);
lean_dec(v_ematchDiagSource_1092_);
lean_dec(v_sTerms_1090_);
lean_dec(v_generation_1088_);
lean_dec(v_idx_1087_);
lean_dec(v_size_1082_);
lean_dec(v_proof_x3f_1080_);
lean_dec(v_target_x3f_1079_);
lean_dec_ref(v_congr_1078_);
lean_dec_ref(v_root_1077_);
lean_dec_ref(v_next_1076_);
lean_dec_ref(v_self_1075_);
v_as_x27_1056_ = v_tail_1071_;
v_b_1057_ = v___x_1096_;
goto _start;
}
else
{
lean_object* v___x_1100_; 
lean_inc(v___x_1055_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 9, v___x_1055_);
v___x_1100_ = v___x_1094_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_self_1075_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_next_1076_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_root_1077_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_congr_1078_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v_target_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1104_, 5, v_proof_x3f_1080_);
lean_ctor_set(v_reuseFailAlloc_1104_, 6, v_size_1082_);
lean_ctor_set(v_reuseFailAlloc_1104_, 7, v_idx_1087_);
lean_ctor_set(v_reuseFailAlloc_1104_, 8, v_generation_1088_);
lean_ctor_set(v_reuseFailAlloc_1104_, 9, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1104_, 10, v_sTerms_1090_);
lean_ctor_set(v_reuseFailAlloc_1104_, 11, v_ematchDiagSource_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*12, v_flipped_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*12 + 1, v_interpreted_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*12 + 2, v_ctor_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*12 + 3, v_hasLambdas_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*12 + 4, v_heqProofs_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*12 + 5, v_funCC_1091_);
v___x_1100_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; 
lean_inc(v_head_1070_);
v___x_1101_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1070_, v___x_1100_, v___y_1058_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v___x_1102_; 
lean_dec_ref_known(v___x_1101_, 1);
v___x_1102_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1070_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_dec_ref_known(v___x_1102_, 1);
v_as_x27_1056_ = v_tail_1071_;
v_b_1057_ = v___x_1096_;
goto _start;
}
else
{
lean_dec(v___x_1055_);
return v___x_1102_;
}
}
else
{
lean_dec(v___x_1055_);
return v___x_1101_;
}
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec(v___x_1055_);
v_a_1106_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1073_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1073_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_st_ref_get(v_a_1115_);
v___x_1127_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1114_, v_a_1115_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_toGoalState_1128_; lean_object* v_ematch_1129_; lean_object* v_a_1130_; lean_object* v_gmt_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_toGoalState_1128_ = lean_ctor_get(v___x_1126_, 0);
lean_inc_ref(v_toGoalState_1128_);
lean_dec(v___x_1126_);
v_ematch_1129_ = lean_ctor_get(v_toGoalState_1128_, 12);
lean_inc_ref(v_ematch_1129_);
lean_dec_ref(v_toGoalState_1128_);
v_a_1130_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1127_, 1);
v_gmt_1131_ = lean_ctor_get(v_ematch_1129_, 1);
lean_inc(v_gmt_1131_);
lean_dec_ref(v_ematch_1129_);
v___x_1132_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1130_);
lean_dec(v_a_1130_);
v___x_1133_ = lean_box(0);
v___x_1134_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1131_, v___x_1132_, v___x_1133_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
lean_dec(v___x_1132_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v___x_1134_, 0);
lean_dec(v_unused_1142_);
v___x_1136_ = v___x_1134_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_dec(v___x_1134_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1133_);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1133_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
return v___x_1134_;
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v___x_1126_);
v_a_1143_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1127_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1127_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_root_1151_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1164_, lean_object* v_as_x27_1165_, lean_object* v_b_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1164_, v_as_x27_1165_, v_b_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec(v_as_x27_1165_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1179_, lean_object* v_as_1180_, lean_object* v_as_x27_1181_, lean_object* v_b_1182_, lean_object* v_a_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1179_, v_as_x27_1181_, v_b_1182_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1196_, lean_object* v_as_1197_, lean_object* v_as_x27_1198_, lean_object* v_b_1199_, lean_object* v_a_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1196_, v_as_1197_, v_as_x27_1198_, v_b_1199_, v_a_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec(v_as_x27_1198_);
lean_dec(v_as_1197_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
if (lean_obj_tag(v_a_1213_) == 0)
{
lean_object* v___x_1215_; 
v___x_1215_ = l_List_reverse___redArg(v_a_1214_);
return v___x_1215_;
}
else
{
lean_object* v_head_1216_; lean_object* v_tail_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1226_; 
v_head_1216_ = lean_ctor_get(v_a_1213_, 0);
v_tail_1217_ = lean_ctor_get(v_a_1213_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_a_1213_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1219_ = v_a_1213_;
v_isShared_1220_ = v_isSharedCheck_1226_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_tail_1217_);
lean_inc(v_head_1216_);
lean_dec(v_a_1213_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1226_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = l_Lean_MessageData_ofExpr(v_head_1216_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v_a_1214_);
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_a_1214_);
v___x_1223_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
v_a_1213_ = v_tail_1217_;
v_a_1214_ = v___x_1223_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_fst_1230_, lean_object* v_lams_1231_, lean_object* v_____r_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1227_, v_a_1228_, v___y_1233_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; uint8_t v___x_1293_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v___x_1293_ = lean_unbox(v_a_1292_);
lean_dec(v_a_1292_);
if (v___x_1293_ == 0)
{
v___y_1245_ = v___y_1233_;
v___y_1246_ = v___y_1234_;
v___y_1247_ = v___y_1235_;
v___y_1248_ = v___y_1236_;
v___y_1249_ = v___y_1237_;
v___y_1250_ = v___y_1238_;
v___y_1251_ = v___y_1239_;
v___y_1252_ = v___y_1240_;
v___y_1253_ = v___y_1241_;
v___y_1254_ = v___y_1242_;
goto v___jp_1244_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_inc(v_fst_1230_);
v___x_1294_ = l_Array_reverse___redArg(v_fst_1230_);
lean_inc(v_snd_1227_);
v___x_1295_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1231_, v_snd_1227_, v___x_1294_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_dec_ref_known(v___x_1295_, 1);
v___y_1245_ = v___y_1233_;
v___y_1246_ = v___y_1234_;
v___y_1247_ = v___y_1235_;
v___y_1248_ = v___y_1236_;
v___y_1249_ = v___y_1237_;
v___y_1250_ = v___y_1238_;
v___y_1251_ = v___y_1239_;
v___y_1252_ = v___y_1240_;
v___y_1253_ = v___y_1241_;
v___y_1254_ = v___y_1242_;
goto v___jp_1244_;
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_fst_1230_);
lean_dec(v_snd_1227_);
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
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
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_fst_1230_);
lean_dec(v_snd_1227_);
v_a_1304_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1291_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1291_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
v___jp_1244_:
{
if (lean_obj_tag(v_snd_1227_) == 5)
{
lean_object* v_fn_1255_; lean_object* v_arg_1256_; lean_object* v___x_1257_; 
v_fn_1255_ = lean_ctor_get(v_snd_1227_, 0);
lean_inc_ref(v_fn_1255_);
v_arg_1256_ = lean_ctor_get(v_snd_1227_, 1);
lean_inc_ref(v_arg_1256_);
v___x_1257_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1229_, v___y_1245_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1257_, 1);
v___x_1259_ = lean_box(0);
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc(v___y_1245_);
v___x_1260_ = lean_grind_internalize(v_snd_1227_, v_a_1258_, v___x_1259_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1270_; 
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v___x_1260_, 0);
lean_dec(v_unused_1271_);
v___x_1262_ = v___x_1260_;
v_isShared_1263_ = v_isSharedCheck_1270_;
goto v_resetjp_1261_;
}
else
{
lean_dec(v___x_1260_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1270_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1264_ = lean_array_push(v_fst_1230_, v_arg_1256_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v_fn_1255_);
v___x_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1266_);
v___x_1268_ = v___x_1262_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_arg_1256_);
lean_dec_ref(v_fn_1255_);
lean_dec(v_fst_1230_);
v_a_1272_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1260_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1260_);
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
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v_arg_1256_);
lean_dec_ref(v_fn_1255_);
lean_dec_ref_known(v_snd_1227_, 2);
lean_dec(v_fst_1230_);
v_a_1280_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1257_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1257_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v_fst_1230_);
lean_ctor_set(v___x_1288_, 1, v_snd_1227_);
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1312_ = _args[0];
lean_object* v_a_1313_ = _args[1];
lean_object* v_a_1314_ = _args[2];
lean_object* v_fst_1315_ = _args[3];
lean_object* v_lams_1316_ = _args[4];
lean_object* v_____r_1317_ = _args[5];
lean_object* v___y_1318_ = _args[6];
lean_object* v___y_1319_ = _args[7];
lean_object* v___y_1320_ = _args[8];
lean_object* v___y_1321_ = _args[9];
lean_object* v___y_1322_ = _args[10];
lean_object* v___y_1323_ = _args[11];
lean_object* v___y_1324_ = _args[12];
lean_object* v___y_1325_ = _args[13];
lean_object* v___y_1326_ = _args[14];
lean_object* v___y_1327_ = _args[15];
lean_object* v___y_1328_ = _args[16];
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1312_, v_a_1313_, v_a_1314_, v_fst_1315_, v_lams_1316_, v_____r_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v_lams_1316_);
lean_dec_ref(v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1329_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1336_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1337_ = l_Lean_Name_append(v___x_1336_, v___x_1335_);
return v___x_1337_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_lams_1343_, lean_object* v_a_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___y_1357_; lean_object* v_options_1377_; lean_object* v_fst_1378_; lean_object* v_snd_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1416_; 
v_options_1377_ = lean_ctor_get(v___y_1353_, 2);
v_fst_1378_ = lean_ctor_get(v_a_1344_, 0);
v_snd_1379_ = lean_ctor_get(v_a_1344_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_a_1344_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1381_ = v_a_1344_;
v_isShared_1382_ = v_isSharedCheck_1416_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_snd_1379_);
lean_inc(v_fst_1378_);
lean_dec(v_a_1344_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1416_;
goto v_resetjp_1380_;
}
v___jp_1356_:
{
if (lean_obj_tag(v___y_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1368_; 
v_a_1358_ = lean_ctor_get(v___y_1357_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___y_1357_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1360_ = v___y_1357_;
v_isShared_1361_ = v_isSharedCheck_1368_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___y_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1368_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
if (lean_obj_tag(v_a_1358_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; 
v_a_1362_ = lean_ctor_get(v_a_1358_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v_a_1358_, 1);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v_a_1362_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
else
{
lean_object* v_a_1366_; 
lean_del_object(v___x_1360_);
v_a_1366_ = lean_ctor_get(v_a_1358_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v_a_1358_, 1);
v_a_1344_ = v_a_1366_;
goto _start;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_a_1369_ = lean_ctor_get(v___y_1357_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___y_1357_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___y_1357_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___y_1357_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
v_resetjp_1380_:
{
lean_object* v_inheritedTraceOptions_1383_; uint8_t v_hasTrace_1384_; 
v_inheritedTraceOptions_1383_ = lean_ctor_get(v___y_1353_, 13);
v_hasTrace_1384_ = lean_ctor_get_uint8(v_options_1377_, sizeof(void*)*1);
if (v_hasTrace_1384_ == 0)
{
lean_del_object(v___x_1381_);
goto v___jp_1385_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1388_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1389_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1390_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1383_, v_options_1377_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_del_object(v___x_1381_);
goto v___jp_1385_;
}
else
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_Meta_Grind_updateLastTag(v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_dec_ref_known(v___x_1391_, 1);
v___x_1392_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1379_);
v___x_1393_ = l_Lean_MessageData_ofExpr(v_snd_1379_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 7);
lean_ctor_set(v___x_1381_, 1, v___x_1393_);
lean_ctor_set(v___x_1381_, 0, v___x_1392_);
v___x_1395_ = v___x_1381_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1388_, v___x_1395_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1398_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1398_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1379_, v_a_1342_, v_a_1341_, v_fst_1378_, v_lams_1343_, v_a_1397_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
v___y_1357_ = v___x_1398_;
goto v___jp_1356_;
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_snd_1379_);
lean_dec(v_fst_1378_);
v_a_1399_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1396_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1396_);
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
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_dec(v_fst_1378_);
v_a_1408_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1391_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1391_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
v___jp_1385_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1379_, v_a_1342_, v_a_1341_, v_fst_1378_, v_lams_1343_, v___x_1386_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
v___y_1357_ = v___x_1387_;
goto v___jp_1356_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_lams_1419_, lean_object* v_a_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1417_, v_a_1418_, v_lams_1419_, v_a_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v_lams_1419_);
lean_dec_ref(v_a_1418_);
lean_dec_ref(v_a_1417_);
return v_res_1432_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1437_ = l_Lean_stringToMessageData(v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1438_, lean_object* v_lams_1439_, lean_object* v_as_x27_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
if (lean_obj_tag(v_as_x27_1440_) == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v_b_1441_);
return v___x_1453_;
}
else
{
lean_object* v_options_1454_; lean_object* v_head_1455_; lean_object* v_tail_1456_; lean_object* v_inheritedTraceOptions_1457_; uint8_t v_hasTrace_1458_; lean_object* v___x_1459_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___x_1483_; uint8_t v_a_1485_; 
v_options_1454_ = lean_ctor_get(v___y_1450_, 2);
v_head_1455_ = lean_ctor_get(v_as_x27_1440_, 0);
v_tail_1456_ = lean_ctor_get(v_as_x27_1440_, 1);
v_inheritedTraceOptions_1457_ = lean_ctor_get(v___y_1450_, 13);
v_hasTrace_1458_ = lean_ctor_get_uint8(v_options_1454_, sizeof(void*)*1);
v___x_1459_ = lean_box(0);
v___x_1483_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
if (v_hasTrace_1458_ == 0)
{
v_a_1485_ = v_hasTrace_1458_;
goto v___jp_1484_;
}
else
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1493_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1457_, v_options_1454_, v___x_1492_);
v_a_1485_ = v___x_1493_;
goto v___jp_1484_;
}
v___jp_1460_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_inc(v_head_1455_);
lean_inc_ref(v___y_1461_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___y_1461_);
lean_ctor_set(v___x_1472_, 1, v_head_1455_);
v___x_1473_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1455_, v_a_1438_, v_lams_1439_, v___x_1472_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_dec_ref_known(v___x_1473_, 1);
v_as_x27_1440_ = v_tail_1456_;
v_b_1441_ = v___x_1459_;
goto _start;
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_a_1475_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1473_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1473_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
v___jp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1485_ == 0)
{
v___y_1461_ = v___x_1486_;
v___y_1462_ = v___y_1442_;
v___y_1463_ = v___y_1443_;
v___y_1464_ = v___y_1444_;
v___y_1465_ = v___y_1445_;
v___y_1466_ = v___y_1446_;
v___y_1467_ = v___y_1447_;
v___y_1468_ = v___y_1448_;
v___y_1469_ = v___y_1449_;
v___y_1470_ = v___y_1450_;
v___y_1471_ = v___y_1451_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Meta_Grind_updateLastTag(v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec_ref_known(v___x_1487_, 1);
v___x_1488_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1455_);
v___x_1489_ = l_Lean_MessageData_ofExpr(v_head_1455_);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1483_, v___x_1490_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_dec_ref_known(v___x_1491_, 1);
v___y_1461_ = v___x_1486_;
v___y_1462_ = v___y_1442_;
v___y_1463_ = v___y_1443_;
v___y_1464_ = v___y_1444_;
v___y_1465_ = v___y_1445_;
v___y_1466_ = v___y_1446_;
v___y_1467_ = v___y_1447_;
v___y_1468_ = v___y_1448_;
v___y_1469_ = v___y_1449_;
v___y_1470_ = v___y_1450_;
v___y_1471_ = v___y_1451_;
goto v___jp_1460_;
}
else
{
return v___x_1491_;
}
}
else
{
return v___x_1487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1494_, lean_object* v_lams_1495_, lean_object* v_as_x27_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1494_, v_lams_1495_, v_as_x27_1496_, v_b_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec(v_as_x27_1496_);
lean_dec_ref(v_lams_1495_);
lean_dec_ref(v_a_1494_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1510_, lean_object* v_lams_1511_, lean_object* v_as_1512_, lean_object* v_as_x27_1513_, lean_object* v_b_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
if (lean_obj_tag(v_as_x27_1513_) == 0)
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_b_1514_);
return v___x_1526_;
}
else
{
lean_object* v_options_1527_; lean_object* v_head_1528_; lean_object* v_tail_1529_; lean_object* v_inheritedTraceOptions_1530_; uint8_t v_hasTrace_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; uint8_t v_a_1558_; 
v_options_1527_ = lean_ctor_get(v___y_1523_, 2);
v_head_1528_ = lean_ctor_get(v_as_x27_1513_, 0);
v_tail_1529_ = lean_ctor_get(v_as_x27_1513_, 1);
v_inheritedTraceOptions_1530_ = lean_ctor_get(v___y_1523_, 13);
v_hasTrace_1531_ = lean_ctor_get_uint8(v_options_1527_, sizeof(void*)*1);
v___x_1532_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1533_ = lean_box(0);
if (v_hasTrace_1531_ == 0)
{
v_a_1558_ = v_hasTrace_1531_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1566_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1530_, v_options_1527_, v___x_1565_);
v_a_1558_ = v___x_1566_;
goto v___jp_1557_;
}
v___jp_1534_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_inc(v_head_1528_);
lean_inc_ref(v___y_1535_);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___y_1535_);
lean_ctor_set(v___x_1546_, 1, v_head_1528_);
v___x_1547_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1528_, v_a_1510_, v_lams_1511_, v___x_1546_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; 
lean_dec_ref_known(v___x_1547_, 1);
v___x_1548_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1510_, v_lams_1511_, v_tail_1529_, v___x_1533_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
return v___x_1548_;
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1547_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1547_);
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
v___jp_1557_:
{
lean_object* v___x_1559_; 
v___x_1559_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1558_ == 0)
{
v___y_1535_ = v___x_1559_;
v___y_1536_ = v___y_1515_;
v___y_1537_ = v___y_1516_;
v___y_1538_ = v___y_1517_;
v___y_1539_ = v___y_1518_;
v___y_1540_ = v___y_1519_;
v___y_1541_ = v___y_1520_;
v___y_1542_ = v___y_1521_;
v___y_1543_ = v___y_1522_;
v___y_1544_ = v___y_1523_;
v___y_1545_ = v___y_1524_;
goto v___jp_1534_;
}
else
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Meta_Grind_updateLastTag(v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref_known(v___x_1560_, 1);
v___x_1561_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1528_);
v___x_1562_ = l_Lean_MessageData_ofExpr(v_head_1528_);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1532_, v___x_1563_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_dec_ref_known(v___x_1564_, 1);
v___y_1535_ = v___x_1559_;
v___y_1536_ = v___y_1515_;
v___y_1537_ = v___y_1516_;
v___y_1538_ = v___y_1517_;
v___y_1539_ = v___y_1518_;
v___y_1540_ = v___y_1519_;
v___y_1541_ = v___y_1520_;
v___y_1542_ = v___y_1521_;
v___y_1543_ = v___y_1522_;
v___y_1544_ = v___y_1523_;
v___y_1545_ = v___y_1524_;
goto v___jp_1534_;
}
else
{
return v___x_1564_;
}
}
else
{
return v___x_1560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1567_, lean_object* v_lams_1568_, lean_object* v_as_1569_, lean_object* v_as_x27_1570_, lean_object* v_b_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1567_, v_lams_1568_, v_as_1569_, v_as_x27_1570_, v_b_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec(v_as_x27_1570_);
lean_dec(v_as_1569_);
lean_dec_ref(v_lams_1568_);
lean_dec_ref(v_a_1567_);
return v_res_1583_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1590_, lean_object* v_lams_1591_, lean_object* v_as_1592_, size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_usize_dec_lt(v_i_1594_, v_sz_1593_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_b_1595_);
return v___x_1608_;
}
else
{
lean_object* v_options_1609_; lean_object* v_inheritedTraceOptions_1610_; uint8_t v_hasTrace_1611_; lean_object* v___x_1612_; lean_object* v_a_1613_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; 
v_options_1609_ = lean_ctor_get(v___y_1604_, 2);
v_inheritedTraceOptions_1610_ = lean_ctor_get(v___y_1604_, 13);
v_hasTrace_1611_ = lean_ctor_get_uint8(v_options_1609_, sizeof(void*)*1);
v___x_1612_ = lean_box(0);
v_a_1613_ = lean_array_uget_borrowed(v_as_1592_, v_i_1594_);
if (v_hasTrace_1611_ == 0)
{
v___y_1615_ = v___y_1596_;
v___y_1616_ = v___y_1597_;
v___y_1617_ = v___y_1598_;
v___y_1618_ = v___y_1599_;
v___y_1619_ = v___y_1600_;
v___y_1620_ = v___y_1601_;
v___y_1621_ = v___y_1602_;
v___y_1622_ = v___y_1603_;
v___y_1623_ = v___y_1604_;
v___y_1624_ = v___y_1605_;
goto v___jp_1614_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1640_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1641_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1642_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1610_, v_options_1609_, v___x_1641_);
if (v___x_1642_ == 0)
{
v___y_1615_ = v___y_1596_;
v___y_1616_ = v___y_1597_;
v___y_1617_ = v___y_1598_;
v___y_1618_ = v___y_1599_;
v___y_1619_ = v___y_1600_;
v___y_1620_ = v___y_1601_;
v___y_1621_ = v___y_1602_;
v___y_1622_ = v___y_1603_;
v___y_1623_ = v___y_1604_;
v___y_1624_ = v___y_1605_;
goto v___jp_1614_;
}
else
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Meta_Grind_updateLastTag(v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1644_; 
lean_dec_ref_known(v___x_1643_, 1);
v___x_1644_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1613_, v___y_1596_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1613_);
v___x_1647_ = l_Lean_MessageData_ofExpr(v_a_1613_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1645_);
lean_dec(v_a_1645_);
v___x_1652_ = lean_box(0);
v___x_1653_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1651_, v___x_1652_);
v___x_1654_ = l_Lean_MessageData_ofList(v___x_1653_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1650_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1640_, v___x_1655_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_dec_ref_known(v___x_1656_, 1);
v___y_1615_ = v___y_1596_;
v___y_1616_ = v___y_1597_;
v___y_1617_ = v___y_1598_;
v___y_1618_ = v___y_1599_;
v___y_1619_ = v___y_1600_;
v___y_1620_ = v___y_1601_;
v___y_1621_ = v___y_1602_;
v___y_1622_ = v___y_1603_;
v___y_1623_ = v___y_1604_;
v___y_1624_ = v___y_1605_;
goto v___jp_1614_;
}
else
{
return v___x_1656_;
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_a_1657_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1644_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1644_);
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
else
{
return v___x_1643_;
}
}
}
v___jp_1614_:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1613_, v___y_1615_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1627_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1626_);
lean_dec(v_a_1626_);
v___x_1628_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1590_, v_lams_1591_, v___x_1627_, v___x_1627_, v___x_1612_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___x_1627_);
if (lean_obj_tag(v___x_1628_) == 0)
{
size_t v___x_1629_; size_t v___x_1630_; 
lean_dec_ref_known(v___x_1628_, 1);
v___x_1629_ = ((size_t)1ULL);
v___x_1630_ = lean_usize_add(v_i_1594_, v___x_1629_);
v_i_1594_ = v___x_1630_;
v_b_1595_ = v___x_1612_;
goto _start;
}
else
{
return v___x_1628_;
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1625_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1625_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1665_ = _args[0];
lean_object* v_lams_1666_ = _args[1];
lean_object* v_as_1667_ = _args[2];
lean_object* v_sz_1668_ = _args[3];
lean_object* v_i_1669_ = _args[4];
lean_object* v_b_1670_ = _args[5];
lean_object* v___y_1671_ = _args[6];
lean_object* v___y_1672_ = _args[7];
lean_object* v___y_1673_ = _args[8];
lean_object* v___y_1674_ = _args[9];
lean_object* v___y_1675_ = _args[10];
lean_object* v___y_1676_ = _args[11];
lean_object* v___y_1677_ = _args[12];
lean_object* v___y_1678_ = _args[13];
lean_object* v___y_1679_ = _args[14];
lean_object* v___y_1680_ = _args[15];
lean_object* v___y_1681_ = _args[16];
_start:
{
size_t v_sz_boxed_1682_; size_t v_i_boxed_1683_; lean_object* v_res_1684_; 
v_sz_boxed_1682_ = lean_unbox_usize(v_sz_1668_);
lean_dec(v_sz_1668_);
v_i_boxed_1683_ = lean_unbox_usize(v_i_1669_);
lean_dec(v_i_1669_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1665_, v_lams_1666_, v_as_1667_, v_sz_boxed_1682_, v_i_boxed_1683_, v_b_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v_as_1667_);
lean_dec_ref(v_lams_1666_);
lean_dec_ref(v_a_1665_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1685_, lean_object* v_lams_1686_, lean_object* v_as_1687_, size_t v_sz_1688_, size_t v_i_1689_, lean_object* v_b_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_usize_dec_lt(v_i_1689_, v_sz_1688_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_b_1690_);
return v___x_1703_;
}
else
{
lean_object* v_options_1704_; lean_object* v_inheritedTraceOptions_1705_; uint8_t v_hasTrace_1706_; lean_object* v___x_1707_; lean_object* v_a_1708_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; 
v_options_1704_ = lean_ctor_get(v___y_1699_, 2);
v_inheritedTraceOptions_1705_ = lean_ctor_get(v___y_1699_, 13);
v_hasTrace_1706_ = lean_ctor_get_uint8(v_options_1704_, sizeof(void*)*1);
v___x_1707_ = lean_box(0);
v_a_1708_ = lean_array_uget_borrowed(v_as_1687_, v_i_1689_);
if (v_hasTrace_1706_ == 0)
{
v___y_1710_ = v___y_1691_;
v___y_1711_ = v___y_1692_;
v___y_1712_ = v___y_1693_;
v___y_1713_ = v___y_1694_;
v___y_1714_ = v___y_1695_;
v___y_1715_ = v___y_1696_;
v___y_1716_ = v___y_1697_;
v___y_1717_ = v___y_1698_;
v___y_1718_ = v___y_1699_;
v___y_1719_ = v___y_1700_;
goto v___jp_1709_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1735_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1736_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1737_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1705_, v_options_1704_, v___x_1736_);
if (v___x_1737_ == 0)
{
v___y_1710_ = v___y_1691_;
v___y_1711_ = v___y_1692_;
v___y_1712_ = v___y_1693_;
v___y_1713_ = v___y_1694_;
v___y_1714_ = v___y_1695_;
v___y_1715_ = v___y_1696_;
v___y_1716_ = v___y_1697_;
v___y_1717_ = v___y_1698_;
v___y_1718_ = v___y_1699_;
v___y_1719_ = v___y_1700_;
goto v___jp_1709_;
}
else
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Meta_Grind_updateLastTag(v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v___x_1739_; 
lean_dec_ref_known(v___x_1738_, 1);
v___x_1739_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1708_, v___y_1691_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1708_);
v___x_1742_ = l_Lean_MessageData_ofExpr(v_a_1708_);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1741_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1740_);
lean_dec(v_a_1740_);
v___x_1747_ = lean_box(0);
v___x_1748_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1746_, v___x_1747_);
v___x_1749_ = l_Lean_MessageData_ofList(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1745_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
v___x_1751_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1735_, v___x_1750_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_dec_ref_known(v___x_1751_, 1);
v___y_1710_ = v___y_1691_;
v___y_1711_ = v___y_1692_;
v___y_1712_ = v___y_1693_;
v___y_1713_ = v___y_1694_;
v___y_1714_ = v___y_1695_;
v___y_1715_ = v___y_1696_;
v___y_1716_ = v___y_1697_;
v___y_1717_ = v___y_1698_;
v___y_1718_ = v___y_1699_;
v___y_1719_ = v___y_1700_;
goto v___jp_1709_;
}
else
{
return v___x_1751_;
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_a_1752_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1739_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1739_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
return v___x_1738_;
}
}
}
v___jp_1709_:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1708_, v___y_1710_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1721_);
lean_dec(v_a_1721_);
v___x_1723_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1685_, v_lams_1686_, v___x_1722_, v___x_1722_, v___x_1707_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___x_1722_);
if (lean_obj_tag(v___x_1723_) == 0)
{
size_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; 
lean_dec_ref_known(v___x_1723_, 1);
v___x_1724_ = ((size_t)1ULL);
v___x_1725_ = lean_usize_add(v_i_1689_, v___x_1724_);
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1685_, v_lams_1686_, v_as_1687_, v_sz_1688_, v___x_1725_, v___x_1707_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1726_;
}
else
{
return v___x_1723_;
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_a_1727_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1720_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1720_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1760_ = _args[0];
lean_object* v_lams_1761_ = _args[1];
lean_object* v_as_1762_ = _args[2];
lean_object* v_sz_1763_ = _args[3];
lean_object* v_i_1764_ = _args[4];
lean_object* v_b_1765_ = _args[5];
lean_object* v___y_1766_ = _args[6];
lean_object* v___y_1767_ = _args[7];
lean_object* v___y_1768_ = _args[8];
lean_object* v___y_1769_ = _args[9];
lean_object* v___y_1770_ = _args[10];
lean_object* v___y_1771_ = _args[11];
lean_object* v___y_1772_ = _args[12];
lean_object* v___y_1773_ = _args[13];
lean_object* v___y_1774_ = _args[14];
lean_object* v___y_1775_ = _args[15];
lean_object* v___y_1776_ = _args[16];
_start:
{
size_t v_sz_boxed_1777_; size_t v_i_boxed_1778_; lean_object* v_res_1779_; 
v_sz_boxed_1777_ = lean_unbox_usize(v_sz_1763_);
lean_dec(v_sz_1763_);
v_i_boxed_1778_ = lean_unbox_usize(v_i_1764_);
lean_dec(v_i_1764_);
v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1760_, v_lams_1761_, v_as_1762_, v_sz_boxed_1777_, v_i_boxed_1778_, v_b_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v_as_1762_);
lean_dec_ref(v_lams_1761_);
lean_dec_ref(v_a_1760_);
return v_res_1779_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1782_ = l_Lean_stringToMessageData(v___x_1781_);
return v___x_1782_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1785_ = l_Lean_stringToMessageData(v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1786_, lean_object* v_fns_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1799_ = lean_array_get_size(v_lams_1786_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_nat_dec_eq(v___x_1799_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1802_ = lean_st_ref_get(v_a_1788_);
v___x_1803_ = l_Lean_instInhabitedExpr;
v___x_1804_ = lean_unsigned_to_nat(1u);
v___x_1805_ = lean_nat_sub(v___x_1799_, v___x_1804_);
v___x_1806_ = lean_array_get_borrowed(v___x_1803_, v_lams_1786_, v___x_1805_);
lean_dec(v___x_1805_);
lean_inc(v___x_1806_);
v___x_1807_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1802_, v___x_1806_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
lean_dec(v___x_1802_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v_options_1832_; uint8_t v_hasTrace_1833_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v_options_1832_ = lean_ctor_get(v_a_1796_, 2);
v_hasTrace_1833_ = lean_ctor_get_uint8(v_options_1832_, sizeof(void*)*1);
if (v_hasTrace_1833_ == 0)
{
v___y_1810_ = v_a_1788_;
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
v___y_1814_ = v_a_1792_;
v___y_1815_ = v_a_1793_;
v___y_1816_ = v_a_1794_;
v___y_1817_ = v_a_1795_;
v___y_1818_ = v_a_1796_;
v___y_1819_ = v_a_1797_;
goto v___jp_1809_;
}
else
{
lean_object* v_inheritedTraceOptions_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_inheritedTraceOptions_1834_ = lean_ctor_get(v_a_1796_, 13);
v___x_1835_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1836_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1837_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1834_, v_options_1832_, v___x_1836_);
if (v___x_1837_ == 0)
{
v___y_1810_ = v_a_1788_;
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
v___y_1814_ = v_a_1792_;
v___y_1815_ = v_a_1793_;
v___y_1816_ = v_a_1794_;
v___y_1817_ = v_a_1795_;
v___y_1818_ = v_a_1796_;
v___y_1819_ = v_a_1797_;
goto v___jp_1809_;
}
else
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_Meta_Grind_updateLastTag(v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec_ref_known(v___x_1838_, 1);
v___x_1839_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1787_);
v___x_1840_ = lean_array_to_list(v_fns_1787_);
v___x_1841_ = lean_box(0);
v___x_1842_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1840_, v___x_1841_);
v___x_1843_ = l_Lean_MessageData_ofList(v___x_1842_);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1839_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
lean_inc_ref(v_lams_1786_);
v___x_1847_ = lean_array_to_list(v_lams_1786_);
v___x_1848_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1847_, v___x_1841_);
v___x_1849_ = l_Lean_MessageData_ofList(v___x_1848_);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1846_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1835_, v___x_1850_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_dec_ref_known(v___x_1851_, 1);
v___y_1810_ = v_a_1788_;
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
v___y_1814_ = v_a_1792_;
v___y_1815_ = v_a_1793_;
v___y_1816_ = v_a_1794_;
v___y_1817_ = v_a_1795_;
v___y_1818_ = v_a_1796_;
v___y_1819_ = v_a_1797_;
goto v___jp_1809_;
}
else
{
lean_dec(v_a_1808_);
lean_dec_ref(v_fns_1787_);
lean_dec_ref(v_lams_1786_);
return v___x_1851_;
}
}
else
{
lean_dec(v_a_1808_);
lean_dec_ref(v_fns_1787_);
lean_dec_ref(v_lams_1786_);
return v___x_1838_;
}
}
}
v___jp_1809_:
{
lean_object* v___x_1820_; size_t v_sz_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1820_ = lean_box(0);
v_sz_1821_ = lean_array_size(v_fns_1787_);
v___x_1822_ = ((size_t)0ULL);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1808_, v_lams_1786_, v_fns_1787_, v_sz_1821_, v___x_1822_, v___x_1820_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec_ref(v_fns_1787_);
lean_dec_ref(v_lams_1786_);
lean_dec(v_a_1808_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; 
v_unused_1831_ = lean_ctor_get(v___x_1823_, 0);
lean_dec(v_unused_1831_);
v___x_1825_ = v___x_1823_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_dec(v___x_1823_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1820_);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1820_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
else
{
return v___x_1823_;
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v_fns_1787_);
lean_dec_ref(v_lams_1786_);
v_a_1852_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1807_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1807_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec_ref(v_fns_1787_);
lean_dec_ref(v_lams_1786_);
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
return v___x_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1862_, lean_object* v_fns_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1862_, v_fns_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec(v_a_1864_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_lams_1878_, lean_object* v_inst_1879_, lean_object* v_a_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1876_, v_a_1877_, v_lams_1878_, v_a_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_lams_1895_, lean_object* v_inst_1896_, lean_object* v_a_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1893_, v_a_1894_, v_lams_1895_, v_inst_1896_, v_a_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v_lams_1895_);
lean_dec_ref(v_a_1894_);
lean_dec_ref(v_a_1893_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1910_, lean_object* v_lams_1911_, lean_object* v_as_1912_, lean_object* v_as_x27_1913_, lean_object* v_b_1914_, lean_object* v_a_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1910_, v_lams_1911_, v_as_1912_, v_as_x27_1913_, v_b_1914_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1928_ = _args[0];
lean_object* v_lams_1929_ = _args[1];
lean_object* v_as_1930_ = _args[2];
lean_object* v_as_x27_1931_ = _args[3];
lean_object* v_b_1932_ = _args[4];
lean_object* v_a_1933_ = _args[5];
lean_object* v___y_1934_ = _args[6];
lean_object* v___y_1935_ = _args[7];
lean_object* v___y_1936_ = _args[8];
lean_object* v___y_1937_ = _args[9];
lean_object* v___y_1938_ = _args[10];
lean_object* v___y_1939_ = _args[11];
lean_object* v___y_1940_ = _args[12];
lean_object* v___y_1941_ = _args[13];
lean_object* v___y_1942_ = _args[14];
lean_object* v___y_1943_ = _args[15];
lean_object* v___y_1944_ = _args[16];
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1928_, v_lams_1929_, v_as_1930_, v_as_x27_1931_, v_b_1932_, v_a_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec(v_as_x27_1931_);
lean_dec(v_as_1930_);
lean_dec_ref(v_lams_1929_);
lean_dec_ref(v_a_1928_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1946_, lean_object* v_lams_1947_, lean_object* v_as_1948_, lean_object* v_as_x27_1949_, lean_object* v_b_1950_, lean_object* v_a_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1946_, v_lams_1947_, v_as_x27_1949_, v_b_1950_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1964_ = _args[0];
lean_object* v_lams_1965_ = _args[1];
lean_object* v_as_1966_ = _args[2];
lean_object* v_as_x27_1967_ = _args[3];
lean_object* v_b_1968_ = _args[4];
lean_object* v_a_1969_ = _args[5];
lean_object* v___y_1970_ = _args[6];
lean_object* v___y_1971_ = _args[7];
lean_object* v___y_1972_ = _args[8];
lean_object* v___y_1973_ = _args[9];
lean_object* v___y_1974_ = _args[10];
lean_object* v___y_1975_ = _args[11];
lean_object* v___y_1976_ = _args[12];
lean_object* v___y_1977_ = _args[13];
lean_object* v___y_1978_ = _args[14];
lean_object* v___y_1979_ = _args[15];
lean_object* v___y_1980_ = _args[16];
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1964_, v_lams_1965_, v_as_1966_, v_as_x27_1967_, v_b_1968_, v_a_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec(v_as_x27_1967_);
lean_dec(v_as_1966_);
lean_dec_ref(v_lams_1965_);
lean_dec_ref(v_a_1964_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1985_, lean_object* v_as_1986_, size_t v_sz_1987_, size_t v_i_1988_, lean_object* v_b_1989_){
_start:
{
lean_object* v_a_1991_; uint8_t v___x_1995_; 
v___x_1995_ = lean_usize_dec_lt(v_i_1988_, v_sz_1987_);
if (v___x_1995_ == 0)
{
lean_inc_ref(v_b_1989_);
return v_b_1989_;
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_a_1998_; 
v___x_1996_ = lean_box(0);
v___x_1997_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1998_ = lean_array_uget_borrowed(v_as_1986_, v_i_1988_);
if (lean_obj_tag(v_a_1998_) == 6)
{
lean_object* v_binderType_1999_; uint8_t v___x_2000_; 
v_binderType_1999_ = lean_ctor_get(v_a_1998_, 1);
v___x_2000_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_d_1985_, v_binderType_1999_);
if (v___x_2000_ == 0)
{
v_a_1991_ = v___x_1997_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_inc_ref(v_a_1998_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_a_1998_);
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_1996_);
return v___x_2003_;
}
}
else
{
v_a_1991_ = v___x_1997_;
goto v___jp_1990_;
}
}
v___jp_1990_:
{
size_t v___x_1992_; size_t v___x_1993_; 
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_add(v_i_1988_, v___x_1992_);
v_i_1988_ = v___x_1993_;
v_b_1989_ = v_a_1991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_2004_, lean_object* v_as_2005_, lean_object* v_sz_2006_, lean_object* v_i_2007_, lean_object* v_b_2008_){
_start:
{
size_t v_sz_boxed_2009_; size_t v_i_boxed_2010_; lean_object* v_res_2011_; 
v_sz_boxed_2009_ = lean_unbox_usize(v_sz_2006_);
lean_dec(v_sz_2006_);
v_i_boxed_2010_ = lean_unbox_usize(v_i_2007_);
lean_dec(v_i_2007_);
v_res_2011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2004_, v_as_2005_, v_sz_boxed_2009_, v_i_boxed_2010_, v_b_2008_);
lean_dec_ref(v_b_2008_);
lean_dec_ref(v_as_2005_);
lean_dec_ref(v_d_2004_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2012_, lean_object* v_d_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; size_t v_sz_2016_; size_t v___x_2017_; lean_object* v___x_2018_; lean_object* v_fst_2019_; 
v___x_2014_ = lean_box(0);
v___x_2015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2016_ = lean_array_size(v_lams_2012_);
v___x_2017_ = ((size_t)0ULL);
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2013_, v_lams_2012_, v_sz_2016_, v___x_2017_, v___x_2015_);
v_fst_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_fst_2019_);
lean_dec_ref(v___x_2018_);
if (lean_obj_tag(v_fst_2019_) == 0)
{
return v___x_2014_;
}
else
{
lean_object* v_val_2020_; 
v_val_2020_ = lean_ctor_get(v_fst_2019_, 0);
lean_inc(v_val_2020_);
lean_dec_ref_known(v_fst_2019_, 1);
return v_val_2020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2021_, lean_object* v_d_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2021_, v_d_2022_);
lean_dec_ref(v_d_2022_);
lean_dec_ref(v_lams_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2034_, lean_object* v_lams_u2081_2035_, lean_object* v_as_2036_, size_t v_sz_2037_, size_t v_i_2038_, lean_object* v_b_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_a_2052_; uint8_t v___x_2056_; 
v___x_2056_ = lean_usize_dec_lt(v_i_2038_, v_sz_2037_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_b_2039_);
return v___x_2057_;
}
else
{
lean_object* v___x_2058_; lean_object* v_a_2059_; 
v___x_2058_ = lean_box(0);
v_a_2059_ = lean_array_uget_borrowed(v_as_2036_, v_i_2038_);
if (lean_obj_tag(v_a_2059_) == 6)
{
lean_object* v_binderType_2060_; lean_object* v_body_2061_; lean_object* v___x_2062_; 
v_binderType_2060_ = lean_ctor_get(v_a_2059_, 1);
v_body_2061_ = lean_ctor_get(v_a_2059_, 2);
lean_inc_ref(v_binderType_2060_);
v___x_2062_ = l_Lean_Meta_getLevel(v_binderType_2060_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2065_ = lean_box(0);
v___x_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2066_, 0, v_a_2063_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
lean_inc_ref(v___x_2066_);
v___x_2067_ = l_Lean_mkConst(v___x_2064_, v___x_2066_);
lean_inc_ref(v_binderType_2060_);
v___x_2068_ = l_Lean_Expr_app___override(v___x_2067_, v_binderType_2060_);
v___x_2069_ = lean_box(0);
v___x_2070_ = l_Lean_Meta_synthInstance_x3f(v___x_2068_, v___x_2069_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
if (lean_obj_tag(v_a_2071_) == 1)
{
lean_object* v_val_2072_; lean_object* v___x_2073_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; uint8_t v___x_2138_; 
v_val_2072_ = lean_ctor_get(v_a_2071_, 0);
lean_inc(v_val_2072_);
lean_dec_ref_known(v_a_2071_, 1);
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2138_ = l_Lean_Expr_hasLooseBVars(v_body_2061_);
if (v___x_2138_ == 0)
{
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
v___y_2081_ = v___y_2046_;
v___y_2082_ = v___y_2047_;
v___y_2083_ = v___y_2048_;
v___y_2084_ = v___y_2049_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2066_);
v___x_2140_ = l_Lean_mkConst(v___x_2139_, v___x_2066_);
lean_inc_ref(v_binderType_2060_);
v___x_2141_ = l_Lean_Expr_app___override(v___x_2140_, v_binderType_2060_);
v___x_2142_ = l_Lean_Meta_synthInstance_x3f(v___x_2141_, v___x_2069_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
if (lean_obj_tag(v_a_2143_) == 0)
{
lean_dec(v_val_2072_);
lean_dec_ref_known(v___x_2066_, 2);
v_a_2052_ = v___x_2058_;
goto v___jp_2051_;
}
else
{
lean_dec_ref_known(v_a_2143_, 1);
if (v___x_2138_ == 0)
{
lean_dec(v_val_2072_);
lean_dec_ref_known(v___x_2066_, 2);
v_a_2052_ = v___x_2058_;
goto v___jp_2051_;
}
else
{
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
v___y_2081_ = v___y_2046_;
v___y_2082_ = v___y_2047_;
v___y_2083_ = v___y_2048_;
v___y_2084_ = v___y_2049_;
goto v___jp_2074_;
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_val_2072_);
lean_dec_ref_known(v___x_2066_, 2);
v_a_2144_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2142_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2142_);
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
v___jp_2074_:
{
lean_object* v___x_2085_; 
v___x_2085_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2034_, v_binderType_2060_);
if (lean_obj_tag(v___x_2085_) == 1)
{
lean_object* v_val_2086_; 
v_val_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_val_2086_);
lean_dec_ref_known(v___x_2085_, 1);
if (lean_obj_tag(v_val_2086_) == 6)
{
lean_object* v_binderType_2087_; lean_object* v_body_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_binderType_2087_ = lean_ctor_get(v_val_2086_, 1);
lean_inc_ref(v_binderType_2087_);
v_body_2088_ = lean_ctor_get(v_val_2086_, 2);
lean_inc_ref(v_body_2088_);
lean_dec_ref_known(v_val_2086_, 3);
v___x_2089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2090_ = l_Lean_mkConst(v___x_2089_, v___x_2066_);
v___x_2091_ = l_Lean_mkAppB(v___x_2090_, v_binderType_2087_, v_val_2072_);
v___x_2092_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2091_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = lean_array_fget_borrowed(v_lams_u2081_2035_, v___x_2073_);
v___x_2095_ = lean_array_fget_borrowed(v_lams_u2082_2034_, v___x_2073_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
lean_inc(v___y_2076_);
lean_inc(v___y_2075_);
lean_inc(v___x_2095_);
lean_inc(v___x_2094_);
v___x_2096_ = lean_grind_mk_eq_proof(v___x_2094_, v___x_2095_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = lean_expr_instantiate1(v_body_2061_, v_a_2093_);
v___x_2099_ = lean_expr_instantiate1(v_body_2088_, v_a_2093_);
lean_dec_ref(v_body_2088_);
v___x_2100_ = l_Lean_Meta_mkCongrFun(v_a_2097_, v_a_2093_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = l_Lean_Meta_mkEq(v___x_2098_, v___x_2099_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = l_Lean_Meta_mkExpectedPropHint(v_a_2101_, v_a_2103_);
v___x_2105_ = l_Lean_Meta_Grind_pushNewFact(v___x_2104_, v___x_2073_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_dec_ref_known(v___x_2105_, 1);
v_a_2052_ = v___x_2058_;
goto v___jp_2051_;
}
else
{
return v___x_2105_;
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_a_2101_);
v_a_2106_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2102_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2102_);
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
lean_dec_ref(v___x_2099_);
lean_dec_ref(v___x_2098_);
v_a_2114_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2100_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2100_);
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
lean_dec(v_a_2093_);
lean_dec_ref(v_body_2088_);
v_a_2122_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2096_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2096_);
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
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec_ref(v_body_2088_);
v_a_2130_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2092_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2092_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_dec(v_val_2086_);
lean_dec(v_val_2072_);
lean_dec_ref_known(v___x_2066_, 2);
v_a_2052_ = v___x_2058_;
goto v___jp_2051_;
}
}
else
{
lean_dec(v___x_2085_);
lean_dec(v_val_2072_);
lean_dec_ref_known(v___x_2066_, 2);
v_a_2052_ = v___x_2058_;
goto v___jp_2051_;
}
}
}
else
{
lean_dec(v_a_2071_);
lean_dec_ref_known(v___x_2066_, 2);
v_a_2052_ = v___x_2058_;
goto v___jp_2051_;
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec_ref_known(v___x_2066_, 2);
v_a_2152_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2070_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2070_);
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
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
v_a_2160_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2062_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2062_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
v_a_2052_ = v___x_2058_;
goto v___jp_2051_;
}
}
v___jp_2051_:
{
size_t v___x_2053_; size_t v___x_2054_; 
v___x_2053_ = ((size_t)1ULL);
v___x_2054_ = lean_usize_add(v_i_2038_, v___x_2053_);
v_i_2038_ = v___x_2054_;
v_b_2039_ = v_a_2052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2168_ = _args[0];
lean_object* v_lams_u2081_2169_ = _args[1];
lean_object* v_as_2170_ = _args[2];
lean_object* v_sz_2171_ = _args[3];
lean_object* v_i_2172_ = _args[4];
lean_object* v_b_2173_ = _args[5];
lean_object* v___y_2174_ = _args[6];
lean_object* v___y_2175_ = _args[7];
lean_object* v___y_2176_ = _args[8];
lean_object* v___y_2177_ = _args[9];
lean_object* v___y_2178_ = _args[10];
lean_object* v___y_2179_ = _args[11];
lean_object* v___y_2180_ = _args[12];
lean_object* v___y_2181_ = _args[13];
lean_object* v___y_2182_ = _args[14];
lean_object* v___y_2183_ = _args[15];
lean_object* v___y_2184_ = _args[16];
_start:
{
size_t v_sz_boxed_2185_; size_t v_i_boxed_2186_; lean_object* v_res_2187_; 
v_sz_boxed_2185_ = lean_unbox_usize(v_sz_2171_);
lean_dec(v_sz_2171_);
v_i_boxed_2186_ = lean_unbox_usize(v_i_2172_);
lean_dec(v_i_2172_);
v_res_2187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2168_, v_lams_u2081_2169_, v_as_2170_, v_sz_boxed_2185_, v_i_boxed_2186_, v_b_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v_as_2170_);
lean_dec_ref(v_lams_u2081_2169_);
lean_dec_ref(v_lams_u2082_2168_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2188_, lean_object* v_lams_u2082_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2201_ = lean_array_get_size(v_lams_u2081_2188_);
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = lean_nat_dec_eq(v___x_2201_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_array_get_size(v_lams_u2082_2189_);
v___x_2205_ = lean_nat_dec_eq(v___x_2204_, v___x_2202_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; size_t v_sz_2207_; size_t v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = lean_box(0);
v_sz_2207_ = lean_array_size(v_lams_u2081_2188_);
v___x_2208_ = ((size_t)0ULL);
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2189_, v_lams_u2081_2188_, v_lams_u2081_2188_, v_sz_2207_, v___x_2208_, v___x_2206_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v___x_2209_, 0);
lean_dec(v_unused_2217_);
v___x_2211_ = v___x_2209_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_dec(v___x_2209_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2206_);
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2206_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
else
{
return v___x_2209_;
}
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = lean_box(0);
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
return v___x_2219_;
}
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2222_, lean_object* v_lams_u2082_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2222_, v_lams_u2082_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_lams_u2082_2223_);
lean_dec_ref(v_lams_u2081_2222_);
return v_res_2235_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2236_){
_start:
{
uint8_t v___x_2237_; 
v___x_2237_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2238_){
_start:
{
uint8_t v_res_2239_; lean_object* v_r_2240_; 
v_res_2239_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2238_);
lean_dec_ref(v_x_2238_);
v_r_2240_ = lean_box(v_res_2239_);
return v_r_2240_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2241_, lean_object* v_x_2242_){
_start:
{
uint8_t v___x_2243_; 
v___x_2243_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2244_, lean_object* v_x_2245_){
_start:
{
uint8_t v_res_2246_; lean_object* v_r_2247_; 
v_res_2246_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2244_, v_x_2245_);
lean_dec_ref(v_x_2245_);
v_r_2247_ = lean_box(v_res_2246_);
return v_r_2247_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2248_, lean_object* v_v_2249_, lean_object* v_i_2250_){
_start:
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = lean_array_get_size(v_xs_2248_);
v___x_2252_ = lean_nat_dec_lt(v_i_2250_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
lean_dec(v_i_2250_);
v___x_2253_ = lean_box(0);
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2254_ = lean_array_fget_borrowed(v_xs_2248_, v_i_2250_);
v___x_2255_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2254_, v_v_2249_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_nat_add(v_i_2250_, v___x_2256_);
lean_dec(v_i_2250_);
v_i_2250_ = v___x_2257_;
goto _start;
}
else
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v_i_2250_);
return v___x_2259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2260_, lean_object* v_v_2261_, lean_object* v_i_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2260_, v_v_2261_, v_i_2262_);
lean_dec_ref(v_v_2261_);
lean_dec_ref(v_xs_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2264_, lean_object* v_v_2265_){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2264_, v_v_2265_, v___x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2268_, lean_object* v_v_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2268_, v_v_2269_);
lean_dec_ref(v_v_2269_);
lean_dec_ref(v_xs_2268_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2271_, size_t v_x_2272_, lean_object* v_x_2273_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 0)
{
lean_object* v_es_2274_; lean_object* v___x_2275_; size_t v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; lean_object* v_j_2279_; lean_object* v_entry_2280_; 
v_es_2274_ = lean_ctor_get(v_x_2271_, 0);
v___x_2275_ = lean_box(2);
v___x_2276_ = ((size_t)5ULL);
v___x_2277_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2278_ = lean_usize_land(v_x_2272_, v___x_2277_);
v_j_2279_ = lean_usize_to_nat(v___x_2278_);
v_entry_2280_ = lean_array_get(v___x_2275_, v_es_2274_, v_j_2279_);
switch(lean_obj_tag(v_entry_2280_))
{
case 0:
{
lean_object* v_key_2281_; uint8_t v___x_2282_; 
v_key_2281_ = lean_ctor_get(v_entry_2280_, 0);
lean_inc(v_key_2281_);
lean_dec_ref_known(v_entry_2280_, 2);
v___x_2282_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2273_, v_key_2281_);
lean_dec(v_key_2281_);
if (v___x_2282_ == 0)
{
lean_dec(v_j_2279_);
return v_x_2271_;
}
else
{
lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2290_; 
lean_inc_ref(v_es_2274_);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_x_2271_);
if (v_isSharedCheck_2290_ == 0)
{
lean_object* v_unused_2291_; 
v_unused_2291_ = lean_ctor_get(v_x_2271_, 0);
lean_dec(v_unused_2291_);
v___x_2284_ = v_x_2271_;
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
else
{
lean_dec(v_x_2271_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_array_set(v_es_2274_, v_j_2279_, v___x_2275_);
lean_dec(v_j_2279_);
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
lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2325_; 
lean_inc_ref(v_es_2274_);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_x_2271_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v_x_2271_, 0);
lean_dec(v_unused_2326_);
v___x_2293_ = v_x_2271_;
v_isShared_2294_ = v_isSharedCheck_2325_;
goto v_resetjp_2292_;
}
else
{
lean_dec(v_x_2271_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2325_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v_node_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2324_; 
v_node_2295_ = lean_ctor_get(v_entry_2280_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_entry_2280_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2297_ = v_entry_2280_;
v_isShared_2298_ = v_isSharedCheck_2324_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_node_2295_);
lean_dec(v_entry_2280_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2324_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_entries_2299_; size_t v___x_2300_; lean_object* v_newNode_2301_; lean_object* v___x_2302_; 
v_entries_2299_ = lean_array_set(v_es_2274_, v_j_2279_, v___x_2275_);
v___x_2300_ = lean_usize_shift_right(v_x_2272_, v___x_2276_);
v_newNode_2301_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2295_, v___x_2300_, v_x_2273_);
lean_inc_ref(v_newNode_2301_);
v___x_2302_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2304_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v_newNode_2301_);
v___x_2304_ = v___x_2297_;
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
v___x_2305_ = lean_array_set(v_entries_2299_, v_j_2279_, v___x_2304_);
lean_dec(v_j_2279_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2305_);
v___x_2307_ = v___x_2293_;
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
lean_del_object(v___x_2297_);
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
v___x_2318_ = lean_array_set(v_entries_2299_, v_j_2279_, v___x_2317_);
lean_dec(v_j_2279_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2318_);
v___x_2320_ = v___x_2293_;
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
lean_dec(v_j_2279_);
return v_x_2271_;
}
}
}
else
{
lean_object* v_ks_2327_; lean_object* v_vs_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2342_; 
v_ks_2327_ = lean_ctor_get(v_x_2271_, 0);
v_vs_2328_ = lean_ctor_get(v_x_2271_, 1);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_x_2271_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2330_ = v_x_2271_;
v_isShared_2331_ = v_isSharedCheck_2342_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_vs_2328_);
lean_inc(v_ks_2327_);
lean_dec(v_x_2271_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2342_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2327_, v_x_2273_);
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
size_t v_x_21947__boxed_2346_; lean_object* v_res_2347_; 
v_x_21947__boxed_2346_ = lean_unbox_usize(v_x_2344_);
lean_dec(v_x_2344_);
v_res_2347_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2343_, v_x_21947__boxed_2346_, v_x_2345_);
lean_dec_ref(v_x_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
uint64_t v___x_2350_; size_t v_h_2351_; lean_object* v___x_2352_; 
v___x_2350_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2349_);
v_h_2351_ = lean_uint64_to_usize(v___x_2350_);
v___x_2352_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2348_, v_h_2351_, v_x_2349_);
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
lean_object* v_k_x27_2394_; uint8_t v___x_2395_; 
v_k_x27_2394_ = lean_array_fget_borrowed(v_keys_2387_, v_i_2389_);
v___x_2395_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_2390_, v_k_x27_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_unsigned_to_nat(1u);
v___x_2397_ = lean_nat_add(v_i_2389_, v___x_2396_);
lean_dec(v_i_2389_);
v_i_2389_ = v___x_2397_;
goto _start;
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_array_fget_borrowed(v_vals_2388_, v_i_2389_);
lean_dec(v_i_2389_);
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
lean_object* v_es_2409_; lean_object* v___x_2410_; size_t v___x_2411_; size_t v___x_2412_; size_t v___x_2413_; lean_object* v_j_2414_; lean_object* v___x_2415_; 
v_es_2409_ = lean_ctor_get(v_x_2406_, 0);
v___x_2410_ = lean_box(2);
v___x_2411_ = ((size_t)5ULL);
v___x_2412_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2413_ = lean_usize_land(v_x_2407_, v___x_2412_);
v_j_2414_ = lean_usize_to_nat(v___x_2413_);
v___x_2415_ = lean_array_get_borrowed(v___x_2410_, v_es_2409_, v_j_2414_);
lean_dec(v_j_2414_);
switch(lean_obj_tag(v___x_2415_))
{
case 0:
{
lean_object* v_key_2416_; lean_object* v_val_2417_; uint8_t v___x_2418_; 
v_key_2416_ = lean_ctor_get(v___x_2415_, 0);
v_val_2417_ = lean_ctor_get(v___x_2415_, 1);
v___x_2418_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2408_, v_key_2416_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_box(0);
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; 
lean_inc(v_val_2417_);
v___x_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_val_2417_);
return v___x_2420_;
}
}
case 1:
{
lean_object* v_node_2421_; size_t v___x_2422_; 
v_node_2421_ = lean_ctor_get(v___x_2415_, 0);
v___x_2422_ = lean_usize_shift_right(v_x_2407_, v___x_2411_);
v_x_2406_ = v_node_2421_;
v_x_2407_ = v___x_2422_;
goto _start;
}
default: 
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_box(0);
return v___x_2424_;
}
}
}
else
{
lean_object* v_ks_2425_; lean_object* v_vs_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_ks_2425_ = lean_ctor_get(v_x_2406_, 0);
v_vs_2426_ = lean_ctor_get(v_x_2406_, 1);
v___x_2427_ = lean_unsigned_to_nat(0u);
v___x_2428_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2425_, v_vs_2426_, v___x_2427_, v_x_2408_);
return v___x_2428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2429_, lean_object* v_x_2430_, lean_object* v_x_2431_){
_start:
{
size_t v_x_22166__boxed_2432_; lean_object* v_res_2433_; 
v_x_22166__boxed_2432_ = lean_unbox_usize(v_x_2430_);
lean_dec(v_x_2430_);
v_res_2433_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2429_, v_x_22166__boxed_2432_, v_x_2431_);
lean_dec_ref(v_x_2431_);
lean_dec_ref(v_x_2429_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2434_, lean_object* v_x_2435_){
_start:
{
uint64_t v___x_2436_; size_t v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2435_);
v___x_2437_ = lean_uint64_to_usize(v___x_2436_);
v___x_2438_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2434_, v___x_2437_, v_x_2435_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2439_, lean_object* v_x_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2439_, v_x_2440_);
lean_dec_ref(v_x_2440_);
lean_dec_ref(v_x_2439_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2442_, lean_object* v_b_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
if (lean_obj_tag(v_as_x27_2442_) == 0)
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_b_2443_);
return v___x_2455_;
}
else
{
lean_object* v_head_2456_; lean_object* v_tail_2457_; lean_object* v___x_2458_; lean_object* v_toGoalState_2459_; lean_object* v_ematch_2460_; lean_object* v_delayedThmInsts_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_head_2456_ = lean_ctor_get(v_as_x27_2442_, 0);
v_tail_2457_ = lean_ctor_get(v_as_x27_2442_, 1);
v___x_2458_ = lean_st_ref_get(v___y_2444_);
v_toGoalState_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc_ref(v_toGoalState_2459_);
lean_dec(v___x_2458_);
v_ematch_2460_ = lean_ctor_get(v_toGoalState_2459_, 12);
lean_inc_ref(v_ematch_2460_);
lean_dec_ref(v_toGoalState_2459_);
v_delayedThmInsts_2461_ = lean_ctor_get(v_ematch_2460_, 10);
lean_inc_ref(v_delayedThmInsts_2461_);
lean_dec_ref(v_ematch_2460_);
v___x_2462_ = lean_box(0);
v___x_2463_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2461_, v_head_2456_);
lean_dec_ref(v_delayedThmInsts_2461_);
if (lean_obj_tag(v___x_2463_) == 1)
{
lean_object* v_val_2464_; lean_object* v___x_2465_; lean_object* v_toGoalState_2466_; lean_object* v_ematch_2467_; lean_object* v_mvarId_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2522_; 
v_val_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_val_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v___x_2465_ = lean_st_ref_take(v___y_2444_);
v_toGoalState_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc_ref(v_toGoalState_2466_);
v_ematch_2467_ = lean_ctor_get(v_toGoalState_2466_, 12);
lean_inc_ref(v_ematch_2467_);
v_mvarId_2468_ = lean_ctor_get(v___x_2465_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2522_ == 0)
{
lean_object* v_unused_2523_; 
v_unused_2523_ = lean_ctor_get(v___x_2465_, 0);
lean_dec(v_unused_2523_);
v___x_2470_ = v___x_2465_;
v_isShared_2471_ = v_isSharedCheck_2522_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_mvarId_2468_);
lean_dec(v___x_2465_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2522_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_nextDeclIdx_2472_; lean_object* v_enodeMap_2473_; lean_object* v_exprs_2474_; lean_object* v_parents_2475_; lean_object* v_congrTable_2476_; lean_object* v_appMap_2477_; lean_object* v_indicesFound_2478_; lean_object* v_newFacts_2479_; uint8_t v_inconsistent_2480_; lean_object* v_nextIdx_2481_; lean_object* v_newRawFacts_2482_; lean_object* v_facts_2483_; lean_object* v_extThms_2484_; lean_object* v_inj_2485_; lean_object* v_split_2486_; lean_object* v_clean_2487_; lean_object* v_sstates_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2520_; 
v_nextDeclIdx_2472_ = lean_ctor_get(v_toGoalState_2466_, 0);
v_enodeMap_2473_ = lean_ctor_get(v_toGoalState_2466_, 1);
v_exprs_2474_ = lean_ctor_get(v_toGoalState_2466_, 2);
v_parents_2475_ = lean_ctor_get(v_toGoalState_2466_, 3);
v_congrTable_2476_ = lean_ctor_get(v_toGoalState_2466_, 4);
v_appMap_2477_ = lean_ctor_get(v_toGoalState_2466_, 5);
v_indicesFound_2478_ = lean_ctor_get(v_toGoalState_2466_, 6);
v_newFacts_2479_ = lean_ctor_get(v_toGoalState_2466_, 7);
v_inconsistent_2480_ = lean_ctor_get_uint8(v_toGoalState_2466_, sizeof(void*)*17);
v_nextIdx_2481_ = lean_ctor_get(v_toGoalState_2466_, 8);
v_newRawFacts_2482_ = lean_ctor_get(v_toGoalState_2466_, 9);
v_facts_2483_ = lean_ctor_get(v_toGoalState_2466_, 10);
v_extThms_2484_ = lean_ctor_get(v_toGoalState_2466_, 11);
v_inj_2485_ = lean_ctor_get(v_toGoalState_2466_, 13);
v_split_2486_ = lean_ctor_get(v_toGoalState_2466_, 14);
v_clean_2487_ = lean_ctor_get(v_toGoalState_2466_, 15);
v_sstates_2488_ = lean_ctor_get(v_toGoalState_2466_, 16);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_toGoalState_2466_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; 
v_unused_2521_ = lean_ctor_get(v_toGoalState_2466_, 12);
lean_dec(v_unused_2521_);
v___x_2490_ = v_toGoalState_2466_;
v_isShared_2491_ = v_isSharedCheck_2520_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_sstates_2488_);
lean_inc(v_clean_2487_);
lean_inc(v_split_2486_);
lean_inc(v_inj_2485_);
lean_inc(v_extThms_2484_);
lean_inc(v_facts_2483_);
lean_inc(v_newRawFacts_2482_);
lean_inc(v_nextIdx_2481_);
lean_inc(v_newFacts_2479_);
lean_inc(v_indicesFound_2478_);
lean_inc(v_appMap_2477_);
lean_inc(v_congrTable_2476_);
lean_inc(v_parents_2475_);
lean_inc(v_exprs_2474_);
lean_inc(v_enodeMap_2473_);
lean_inc(v_nextDeclIdx_2472_);
lean_dec(v_toGoalState_2466_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2520_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_thmMap_2492_; lean_object* v_gmt_2493_; lean_object* v_thms_2494_; lean_object* v_newThms_2495_; lean_object* v_numInstances_2496_; lean_object* v_numDelayedInstances_2497_; lean_object* v_num_2498_; lean_object* v_preInstances_2499_; lean_object* v_nextThmIdx_2500_; lean_object* v_matchEqNames_2501_; lean_object* v_delayedThmInsts_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2519_; 
v_thmMap_2492_ = lean_ctor_get(v_ematch_2467_, 0);
v_gmt_2493_ = lean_ctor_get(v_ematch_2467_, 1);
v_thms_2494_ = lean_ctor_get(v_ematch_2467_, 2);
v_newThms_2495_ = lean_ctor_get(v_ematch_2467_, 3);
v_numInstances_2496_ = lean_ctor_get(v_ematch_2467_, 4);
v_numDelayedInstances_2497_ = lean_ctor_get(v_ematch_2467_, 5);
v_num_2498_ = lean_ctor_get(v_ematch_2467_, 6);
v_preInstances_2499_ = lean_ctor_get(v_ematch_2467_, 7);
v_nextThmIdx_2500_ = lean_ctor_get(v_ematch_2467_, 8);
v_matchEqNames_2501_ = lean_ctor_get(v_ematch_2467_, 9);
v_delayedThmInsts_2502_ = lean_ctor_get(v_ematch_2467_, 10);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_ematch_2467_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2504_ = v_ematch_2467_;
v_isShared_2505_ = v_isSharedCheck_2519_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_delayedThmInsts_2502_);
lean_inc(v_matchEqNames_2501_);
lean_inc(v_nextThmIdx_2500_);
lean_inc(v_preInstances_2499_);
lean_inc(v_num_2498_);
lean_inc(v_numDelayedInstances_2497_);
lean_inc(v_numInstances_2496_);
lean_inc(v_newThms_2495_);
lean_inc(v_thms_2494_);
lean_inc(v_gmt_2493_);
lean_inc(v_thmMap_2492_);
lean_dec(v_ematch_2467_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2519_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2502_, v_head_2456_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 10, v___x_2506_);
v___x_2508_ = v___x_2504_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_thmMap_2492_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_gmt_2493_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_thms_2494_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_newThms_2495_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_numInstances_2496_);
lean_ctor_set(v_reuseFailAlloc_2518_, 5, v_numDelayedInstances_2497_);
lean_ctor_set(v_reuseFailAlloc_2518_, 6, v_num_2498_);
lean_ctor_set(v_reuseFailAlloc_2518_, 7, v_preInstances_2499_);
lean_ctor_set(v_reuseFailAlloc_2518_, 8, v_nextThmIdx_2500_);
lean_ctor_set(v_reuseFailAlloc_2518_, 9, v_matchEqNames_2501_);
lean_ctor_set(v_reuseFailAlloc_2518_, 10, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 12, v___x_2508_);
v___x_2510_ = v___x_2490_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_nextDeclIdx_2472_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_enodeMap_2473_);
lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_exprs_2474_);
lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_parents_2475_);
lean_ctor_set(v_reuseFailAlloc_2517_, 4, v_congrTable_2476_);
lean_ctor_set(v_reuseFailAlloc_2517_, 5, v_appMap_2477_);
lean_ctor_set(v_reuseFailAlloc_2517_, 6, v_indicesFound_2478_);
lean_ctor_set(v_reuseFailAlloc_2517_, 7, v_newFacts_2479_);
lean_ctor_set(v_reuseFailAlloc_2517_, 8, v_nextIdx_2481_);
lean_ctor_set(v_reuseFailAlloc_2517_, 9, v_newRawFacts_2482_);
lean_ctor_set(v_reuseFailAlloc_2517_, 10, v_facts_2483_);
lean_ctor_set(v_reuseFailAlloc_2517_, 11, v_extThms_2484_);
lean_ctor_set(v_reuseFailAlloc_2517_, 12, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2517_, 13, v_inj_2485_);
lean_ctor_set(v_reuseFailAlloc_2517_, 14, v_split_2486_);
lean_ctor_set(v_reuseFailAlloc_2517_, 15, v_clean_2487_);
lean_ctor_set(v_reuseFailAlloc_2517_, 16, v_sstates_2488_);
lean_ctor_set_uint8(v_reuseFailAlloc_2517_, sizeof(void*)*17, v_inconsistent_2480_);
v___x_2510_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2512_; 
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2510_);
v___x_2512_ = v___x_2470_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_mvarId_2468_);
v___x_2512_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_st_ref_set(v___y_2444_, v___x_2512_);
v___x_2514_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2464_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_dec_ref_known(v___x_2514_, 1);
v_as_x27_2442_ = v_tail_2457_;
v_b_2443_ = v___x_2462_;
goto _start;
}
else
{
return v___x_2514_;
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
lean_dec(v___x_2463_);
v_as_x27_2442_ = v_tail_2457_;
v_b_2443_ = v___x_2462_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2525_, lean_object* v_b_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2525_, v_b_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec(v_as_x27_2525_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2540_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2580_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2580_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2580_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
uint8_t v___x_2556_; 
v___x_2556_ = lean_unbox(v_a_2552_);
lean_dec(v_a_2552_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; lean_object* v_toGoalState_2558_; lean_object* v_ematch_2559_; lean_object* v_delayedThmInsts_2560_; uint8_t v___x_2561_; 
v___x_2557_ = lean_st_ref_get(v_a_2540_);
v_toGoalState_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc_ref(v_toGoalState_2558_);
lean_dec(v___x_2557_);
v_ematch_2559_ = lean_ctor_get(v_toGoalState_2558_, 12);
lean_inc_ref(v_ematch_2559_);
lean_dec_ref(v_toGoalState_2558_);
v_delayedThmInsts_2560_ = lean_ctor_get(v_ematch_2559_, 10);
lean_inc_ref(v_delayedThmInsts_2560_);
lean_dec_ref(v_ematch_2559_);
v___x_2561_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2560_);
lean_dec_ref(v_delayedThmInsts_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_del_object(v___x_2554_);
v___x_2562_ = lean_box(0);
v___x_2563_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2539_, v___x_2562_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2570_ == 0)
{
lean_object* v_unused_2571_; 
v_unused_2571_ = lean_ctor_get(v___x_2563_, 0);
lean_dec(v_unused_2571_);
v___x_2565_ = v___x_2563_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_dec(v___x_2563_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2562_);
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2562_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
else
{
return v___x_2563_;
}
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2572_ = lean_box(0);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2572_);
v___x_2574_ = v___x_2554_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = lean_box(0);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2576_);
v___x_2578_ = v___x_2554_;
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
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
v_a_2581_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2551_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2551_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec(v_toPropagateDown_2589_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2602_, lean_object* v_x_2603_, lean_object* v_x_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2603_, v_x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2606_, v_x_2607_, v_x_2608_);
lean_dec_ref(v_x_2608_);
lean_dec_ref(v_x_2607_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2610_, lean_object* v_x_2611_, lean_object* v_x_2612_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2611_, v_x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2614_, v_x_2615_, v_x_2616_);
lean_dec_ref(v_x_2616_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2618_, lean_object* v_as_x27_2619_, lean_object* v_b_2620_, lean_object* v_a_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2619_, v_b_2620_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2634_, lean_object* v_as_x27_2635_, lean_object* v_b_2636_, lean_object* v_a_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2634_, v_as_x27_2635_, v_b_2636_, v_a_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec(v_as_x27_2635_);
lean_dec(v_as_2634_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2650_, lean_object* v_x_2651_, size_t v_x_2652_, lean_object* v_x_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2651_, v_x_2652_, v_x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2655_, lean_object* v_x_2656_, lean_object* v_x_2657_, lean_object* v_x_2658_){
_start:
{
size_t v_x_22463__boxed_2659_; lean_object* v_res_2660_; 
v_x_22463__boxed_2659_ = lean_unbox_usize(v_x_2657_);
lean_dec(v_x_2657_);
v_res_2660_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2655_, v_x_2656_, v_x_22463__boxed_2659_, v_x_2658_);
lean_dec_ref(v_x_2658_);
lean_dec_ref(v_x_2656_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2661_, lean_object* v_x_2662_, size_t v_x_2663_, lean_object* v_x_2664_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2662_, v_x_2663_, v_x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2666_, lean_object* v_x_2667_, lean_object* v_x_2668_, lean_object* v_x_2669_){
_start:
{
size_t v_x_22474__boxed_2670_; lean_object* v_res_2671_; 
v_x_22474__boxed_2670_ = lean_unbox_usize(v_x_2668_);
lean_dec(v_x_2668_);
v_res_2671_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2666_, v_x_2667_, v_x_22474__boxed_2670_, v_x_2669_);
lean_dec_ref(v_x_2669_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2672_, lean_object* v_keys_2673_, lean_object* v_vals_2674_, lean_object* v_heq_2675_, lean_object* v_i_2676_, lean_object* v_k_2677_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2673_, v_vals_2674_, v_i_2676_, v_k_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2679_, lean_object* v_keys_2680_, lean_object* v_vals_2681_, lean_object* v_heq_2682_, lean_object* v_i_2683_, lean_object* v_k_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2679_, v_keys_2680_, v_vals_2681_, v_heq_2682_, v_i_2683_, v_k_2684_);
lean_dec_ref(v_k_2684_);
lean_dec_ref(v_vals_2681_);
lean_dec_ref(v_keys_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2686_, lean_object* v_keys_2687_, lean_object* v_vals_2688_, lean_object* v_i_2689_, lean_object* v_k_2690_){
_start:
{
lean_object* v___x_2691_; uint8_t v___x_2692_; 
v___x_2691_ = lean_array_get_size(v_keys_2687_);
v___x_2692_ = lean_nat_dec_lt(v_i_2689_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
lean_dec_ref(v_k_2690_);
lean_dec(v_i_2689_);
v___x_2693_ = lean_box(0);
return v___x_2693_;
}
else
{
lean_object* v_k_x27_2694_; uint8_t v___x_2695_; 
v_k_x27_2694_ = lean_array_fget_borrowed(v_keys_2687_, v_i_2689_);
lean_inc(v_k_x27_2694_);
lean_inc_ref(v_k_2690_);
v___x_2695_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2686_, v_k_2690_, v_k_x27_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_add(v_i_2689_, v___x_2696_);
lean_dec(v_i_2689_);
v_i_2689_ = v___x_2697_;
goto _start;
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
lean_dec_ref(v_k_2690_);
v___x_2699_ = lean_array_fget_borrowed(v_vals_2688_, v_i_2689_);
lean_dec(v_i_2689_);
lean_inc(v___x_2699_);
lean_inc(v_k_x27_2694_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v_k_x27_2694_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2702_, lean_object* v_keys_2703_, lean_object* v_vals_2704_, lean_object* v_i_2705_, lean_object* v_k_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2702_, v_keys_2703_, v_vals_2704_, v_i_2705_, v_k_2706_);
lean_dec_ref(v_vals_2704_);
lean_dec_ref(v_keys_2703_);
lean_dec_ref(v___x_2702_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2708_, lean_object* v_x_2709_, size_t v_x_2710_, lean_object* v_x_2711_){
_start:
{
if (lean_obj_tag(v_x_2709_) == 0)
{
lean_object* v_es_2712_; lean_object* v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; lean_object* v_j_2717_; lean_object* v___x_2718_; 
v_es_2712_ = lean_ctor_get(v_x_2709_, 0);
lean_inc_ref(v_es_2712_);
lean_dec_ref_known(v_x_2709_, 1);
v___x_2713_ = lean_box(2);
v___x_2714_ = ((size_t)5ULL);
v___x_2715_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2716_ = lean_usize_land(v_x_2710_, v___x_2715_);
v_j_2717_ = lean_usize_to_nat(v___x_2716_);
v___x_2718_ = lean_array_get(v___x_2713_, v_es_2712_, v_j_2717_);
lean_dec(v_j_2717_);
lean_dec_ref(v_es_2712_);
switch(lean_obj_tag(v___x_2718_))
{
case 0:
{
lean_object* v_key_2719_; lean_object* v_val_2720_; uint8_t v___x_2721_; 
v_key_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc_n(v_key_2719_, 2);
v_val_2720_ = lean_ctor_get(v___x_2718_, 1);
lean_inc(v_val_2720_);
lean_dec_ref_known(v___x_2718_, 2);
v___x_2721_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2708_, v_x_2711_, v_key_2719_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; 
lean_dec(v_val_2720_);
lean_dec(v_key_2719_);
v___x_2722_ = lean_box(0);
return v___x_2722_;
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v_key_2719_);
lean_ctor_set(v___x_2723_, 1, v_val_2720_);
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
}
case 1:
{
lean_object* v_node_2725_; size_t v___x_2726_; 
v_node_2725_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_node_2725_);
lean_dec_ref_known(v___x_2718_, 1);
v___x_2726_ = lean_usize_shift_right(v_x_2710_, v___x_2714_);
v_x_2709_ = v_node_2725_;
v_x_2710_ = v___x_2726_;
goto _start;
}
default: 
{
lean_object* v___x_2728_; 
lean_dec_ref(v_x_2711_);
v___x_2728_ = lean_box(0);
return v___x_2728_;
}
}
}
else
{
lean_object* v_ks_2729_; lean_object* v_vs_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v_ks_2729_ = lean_ctor_get(v_x_2709_, 0);
lean_inc_ref(v_ks_2729_);
v_vs_2730_ = lean_ctor_get(v_x_2709_, 1);
lean_inc_ref(v_vs_2730_);
lean_dec_ref_known(v_x_2709_, 2);
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2708_, v_ks_2729_, v_vs_2730_, v___x_2731_, v_x_2711_);
lean_dec_ref(v_vs_2730_);
lean_dec_ref(v_ks_2729_);
return v___x_2732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2733_, lean_object* v_x_2734_, lean_object* v_x_2735_, lean_object* v_x_2736_){
_start:
{
size_t v_x_27624__boxed_2737_; lean_object* v_res_2738_; 
v_x_27624__boxed_2737_ = lean_unbox_usize(v_x_2735_);
lean_dec(v_x_2735_);
v_res_2738_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2733_, v_x_2734_, v_x_27624__boxed_2737_, v_x_2736_);
lean_dec_ref(v___x_2733_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2739_, lean_object* v_x_2740_, lean_object* v_x_2741_){
_start:
{
uint64_t v___x_2742_; size_t v___x_2743_; lean_object* v___x_2744_; 
lean_inc_ref(v_x_2741_);
v___x_2742_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2739_, v_x_2741_);
v___x_2743_ = lean_uint64_to_usize(v___x_2742_);
lean_inc_ref(v_x_2740_);
v___x_2744_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2739_, v_x_2740_, v___x_2743_, v_x_2741_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2745_, lean_object* v_x_2746_, lean_object* v_x_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2745_, v_x_2746_, v_x_2747_);
lean_dec_ref(v_x_2746_);
lean_dec_ref(v___x_2745_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
lean_object* v_ks_2754_; lean_object* v_vs_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2779_; 
v_ks_2754_ = lean_ctor_get(v_x_2750_, 0);
v_vs_2755_ = lean_ctor_get(v_x_2750_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_x_2750_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2757_ = v_x_2750_;
v_isShared_2758_ = v_isSharedCheck_2779_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_vs_2755_);
lean_inc(v_ks_2754_);
lean_dec(v_x_2750_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2779_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = lean_array_get_size(v_ks_2754_);
v___x_2760_ = lean_nat_dec_lt(v_x_2751_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
lean_dec(v_x_2751_);
v___x_2761_ = lean_array_push(v_ks_2754_, v_x_2752_);
v___x_2762_ = lean_array_push(v_vs_2755_, v_x_2753_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2762_);
lean_ctor_set(v___x_2757_, 0, v___x_2761_);
v___x_2764_ = v___x_2757_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
else
{
lean_object* v_k_x27_2766_; uint8_t v___x_2767_; 
v_k_x27_2766_ = lean_array_fget_borrowed(v_ks_2754_, v_x_2751_);
lean_inc(v_k_x27_2766_);
lean_inc_ref(v_x_2752_);
v___x_2767_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2749_, v_x_2752_, v_k_x27_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2769_; 
if (v_isShared_2758_ == 0)
{
v___x_2769_ = v___x_2757_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_ks_2754_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_vs_2755_);
v___x_2769_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = lean_unsigned_to_nat(1u);
v___x_2771_ = lean_nat_add(v_x_2751_, v___x_2770_);
lean_dec(v_x_2751_);
v_x_2750_ = v___x_2769_;
v_x_2751_ = v___x_2771_;
goto _start;
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2774_ = lean_array_fset(v_ks_2754_, v_x_2751_, v_x_2752_);
v___x_2775_ = lean_array_fset(v_vs_2755_, v_x_2751_, v_x_2753_);
lean_dec(v_x_2751_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2775_);
lean_ctor_set(v___x_2757_, 0, v___x_2774_);
v___x_2777_ = v___x_2757_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2780_, lean_object* v_x_2781_, lean_object* v_x_2782_, lean_object* v_x_2783_, lean_object* v_x_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2780_, v_x_2781_, v_x_2782_, v_x_2783_, v_x_2784_);
lean_dec_ref(v___x_2780_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2786_, lean_object* v_n_2787_, lean_object* v_k_2788_, lean_object* v_v_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_unsigned_to_nat(0u);
v___x_2791_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2786_, v_n_2787_, v___x_2790_, v_k_2788_, v_v_2789_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2792_, lean_object* v_n_2793_, lean_object* v_k_2794_, lean_object* v_v_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2792_, v_n_2793_, v_k_2794_, v_v_2795_);
lean_dec_ref(v___x_2792_);
return v_res_2796_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2798_, lean_object* v_x_2799_, size_t v_x_2800_, size_t v_x_2801_, lean_object* v_x_2802_, lean_object* v_x_2803_){
_start:
{
if (lean_obj_tag(v_x_2799_) == 0)
{
lean_object* v_es_2804_; size_t v___x_2805_; size_t v___x_2806_; size_t v___x_2807_; size_t v___x_2808_; lean_object* v_j_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_es_2804_ = lean_ctor_get(v_x_2799_, 0);
v___x_2805_ = ((size_t)5ULL);
v___x_2806_ = ((size_t)1ULL);
v___x_2807_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2808_ = lean_usize_land(v_x_2800_, v___x_2807_);
v_j_2809_ = lean_usize_to_nat(v___x_2808_);
v___x_2810_ = lean_array_get_size(v_es_2804_);
v___x_2811_ = lean_nat_dec_lt(v_j_2809_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_dec(v_j_2809_);
lean_dec(v_x_2803_);
lean_dec_ref(v_x_2802_);
return v_x_2799_;
}
else
{
lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2848_; 
lean_inc_ref(v_es_2804_);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_x_2799_);
if (v_isSharedCheck_2848_ == 0)
{
lean_object* v_unused_2849_; 
v_unused_2849_ = lean_ctor_get(v_x_2799_, 0);
lean_dec(v_unused_2849_);
v___x_2813_ = v_x_2799_;
v_isShared_2814_ = v_isSharedCheck_2848_;
goto v_resetjp_2812_;
}
else
{
lean_dec(v_x_2799_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2848_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_v_2815_; lean_object* v___x_2816_; lean_object* v_xs_x27_2817_; lean_object* v___y_2819_; 
v_v_2815_ = lean_array_fget(v_es_2804_, v_j_2809_);
v___x_2816_ = lean_box(0);
v_xs_x27_2817_ = lean_array_fset(v_es_2804_, v_j_2809_, v___x_2816_);
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
lean_inc_ref(v_x_2802_);
v___x_2829_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2798_, v_x_2802_, v_key_2824_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_del_object(v___x_2827_);
v___x_2830_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2824_, v_val_2825_, v_x_2802_, v_x_2803_);
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
lean_ctor_set(v___x_2827_, 1, v_x_2803_);
lean_ctor_set(v___x_2827_, 0, v_x_2802_);
v___x_2833_ = v___x_2827_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_x_2802_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_x_2803_);
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
lean_object* v_node_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2846_; 
v_node_2836_ = lean_ctor_get(v_v_2815_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_v_2815_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2838_ = v_v_2815_;
v_isShared_2839_ = v_isSharedCheck_2846_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_node_2836_);
lean_dec(v_v_2815_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2846_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
size_t v___x_2840_; size_t v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2840_ = lean_usize_shift_right(v_x_2800_, v___x_2805_);
v___x_2841_ = lean_usize_add(v_x_2801_, v___x_2806_);
v___x_2842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2798_, v_node_2836_, v___x_2840_, v___x_2841_, v_x_2802_, v_x_2803_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2842_);
v___x_2844_ = v___x_2838_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
v___y_2819_ = v___x_2844_;
goto v___jp_2818_;
}
}
}
default: 
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2847_, 0, v_x_2802_);
lean_ctor_set(v___x_2847_, 1, v_x_2803_);
v___y_2819_ = v___x_2847_;
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
lean_object* v_ks_2850_; lean_object* v_vs_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2871_; 
v_ks_2850_ = lean_ctor_get(v_x_2799_, 0);
v_vs_2851_ = lean_ctor_get(v_x_2799_, 1);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_x_2799_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2853_ = v_x_2799_;
v_isShared_2854_ = v_isSharedCheck_2871_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_vs_2851_);
lean_inc(v_ks_2850_);
lean_dec(v_x_2799_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2871_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_ks_2850_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_vs_2851_);
v___x_2856_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v_newNode_2857_; uint8_t v___y_2859_; size_t v___x_2865_; uint8_t v___x_2866_; 
v_newNode_2857_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2798_, v___x_2856_, v_x_2802_, v_x_2803_);
v___x_2865_ = ((size_t)7ULL);
v___x_2866_ = lean_usize_dec_le(v___x_2865_, v_x_2801_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v___x_2867_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2857_);
v___x_2868_ = lean_unsigned_to_nat(4u);
v___x_2869_ = lean_nat_dec_lt(v___x_2867_, v___x_2868_);
lean_dec(v___x_2867_);
v___y_2859_ = v___x_2869_;
goto v___jp_2858_;
}
else
{
v___y_2859_ = v___x_2866_;
goto v___jp_2858_;
}
v___jp_2858_:
{
if (v___y_2859_ == 0)
{
lean_object* v_ks_2860_; lean_object* v_vs_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_ks_2860_ = lean_ctor_get(v_newNode_2857_, 0);
lean_inc_ref(v_ks_2860_);
v_vs_2861_ = lean_ctor_get(v_newNode_2857_, 1);
lean_inc_ref(v_vs_2861_);
lean_dec_ref(v_newNode_2857_);
v___x_2862_ = lean_unsigned_to_nat(0u);
v___x_2863_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2864_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2798_, v_x_2801_, v_ks_2860_, v_vs_2861_, v___x_2862_, v___x_2863_);
lean_dec_ref(v_vs_2861_);
lean_dec_ref(v_ks_2860_);
return v___x_2864_;
}
else
{
return v_newNode_2857_;
}
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
size_t v_x_27786__boxed_2907_; size_t v_x_27787__boxed_2908_; lean_object* v_res_2909_; 
v_x_27786__boxed_2907_ = lean_unbox_usize(v_x_2903_);
lean_dec(v_x_2903_);
v_x_27787__boxed_2908_ = lean_unbox_usize(v_x_2904_);
lean_dec(v_x_2904_);
v_res_2909_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2901_, v_x_2902_, v_x_27786__boxed_2907_, v_x_27787__boxed_2908_, v_x_2905_, v_x_2906_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2927_, lean_object* v_rootNew_2928_, uint8_t v_a_2929_, lean_object* v_a_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; lean_object* v_snd_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_3106_; 
v___x_2938_ = lean_st_ref_get(v___y_2931_);
v_snd_2939_ = lean_ctor_get(v_a_2930_, 1);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_a_2930_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; 
v_unused_3107_ = lean_ctor_get(v_a_2930_, 0);
lean_dec(v_unused_3107_);
v___x_2941_ = v_a_2930_;
v_isShared_2942_ = v_isSharedCheck_3106_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_snd_2939_);
lean_dec(v_a_2930_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_3106_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; 
lean_inc(v_snd_2939_);
v___x_2943_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2938_, v_snd_2939_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___x_2938_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_3097_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_3097_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_3097_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v_self_2948_; lean_object* v_next_2949_; lean_object* v_congr_2950_; lean_object* v_target_x3f_2951_; lean_object* v_proof_x3f_2952_; uint8_t v_flipped_2953_; lean_object* v_size_2954_; uint8_t v_interpreted_2955_; uint8_t v_ctor_2956_; uint8_t v_hasLambdas_2957_; uint8_t v_heqProofs_2958_; lean_object* v_idx_2959_; lean_object* v_generation_2960_; lean_object* v_mt_2961_; lean_object* v_sTerms_2962_; uint8_t v_funCC_2963_; lean_object* v_ematchDiagSource_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3095_; 
v_self_2948_ = lean_ctor_get(v_a_2944_, 0);
v_next_2949_ = lean_ctor_get(v_a_2944_, 1);
v_congr_2950_ = lean_ctor_get(v_a_2944_, 3);
v_target_x3f_2951_ = lean_ctor_get(v_a_2944_, 4);
v_proof_x3f_2952_ = lean_ctor_get(v_a_2944_, 5);
v_flipped_2953_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*12);
v_size_2954_ = lean_ctor_get(v_a_2944_, 6);
v_interpreted_2955_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*12 + 1);
v_ctor_2956_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*12 + 2);
v_hasLambdas_2957_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*12 + 3);
v_heqProofs_2958_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*12 + 4);
v_idx_2959_ = lean_ctor_get(v_a_2944_, 7);
v_generation_2960_ = lean_ctor_get(v_a_2944_, 8);
v_mt_2961_ = lean_ctor_get(v_a_2944_, 9);
v_sTerms_2962_ = lean_ctor_get(v_a_2944_, 10);
v_funCC_2963_ = lean_ctor_get_uint8(v_a_2944_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2964_ = lean_ctor_get(v_a_2944_, 11);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_a_2944_);
if (v_isSharedCheck_3095_ == 0)
{
lean_object* v_unused_3096_; 
v_unused_3096_ = lean_ctor_get(v_a_2944_, 2);
lean_dec(v_unused_3096_);
v___x_2966_ = v_a_2944_;
v_isShared_2967_ = v_isSharedCheck_3095_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_ematchDiagSource_2964_);
lean_inc(v_sTerms_2962_);
lean_inc(v_mt_2961_);
lean_inc(v_generation_2960_);
lean_inc(v_idx_2959_);
lean_inc(v_size_2954_);
lean_inc(v_proof_x3f_2952_);
lean_inc(v_target_x3f_2951_);
lean_inc(v_congr_2950_);
lean_inc(v_next_2949_);
lean_inc(v_self_2948_);
lean_dec(v_a_2944_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3095_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; lean_object* v___y_2983_; lean_object* v___x_2993_; 
v___x_2968_ = lean_box(0);
lean_inc(v_ematchDiagSource_2964_);
lean_inc(v_sTerms_2962_);
lean_inc(v_mt_2961_);
lean_inc(v_generation_2960_);
lean_inc(v_idx_2959_);
lean_inc(v_size_2954_);
lean_inc(v_proof_x3f_2952_);
lean_inc(v_target_x3f_2951_);
lean_inc_ref(v_rootNew_2928_);
lean_inc_ref(v_next_2949_);
lean_inc_ref(v_self_2948_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 2, v_rootNew_2928_);
v___x_2993_ = v___x_2966_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_self_2948_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_next_2949_);
lean_ctor_set(v_reuseFailAlloc_3094_, 2, v_rootNew_2928_);
lean_ctor_set(v_reuseFailAlloc_3094_, 3, v_congr_2950_);
lean_ctor_set(v_reuseFailAlloc_3094_, 4, v_target_x3f_2951_);
lean_ctor_set(v_reuseFailAlloc_3094_, 5, v_proof_x3f_2952_);
lean_ctor_set(v_reuseFailAlloc_3094_, 6, v_size_2954_);
lean_ctor_set(v_reuseFailAlloc_3094_, 7, v_idx_2959_);
lean_ctor_set(v_reuseFailAlloc_3094_, 8, v_generation_2960_);
lean_ctor_set(v_reuseFailAlloc_3094_, 9, v_mt_2961_);
lean_ctor_set(v_reuseFailAlloc_3094_, 10, v_sTerms_2962_);
lean_ctor_set(v_reuseFailAlloc_3094_, 11, v_ematchDiagSource_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_3094_, sizeof(void*)*12, v_flipped_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_3094_, sizeof(void*)*12 + 1, v_interpreted_2955_);
lean_ctor_set_uint8(v_reuseFailAlloc_3094_, sizeof(void*)*12 + 2, v_ctor_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_3094_, sizeof(void*)*12 + 3, v_hasLambdas_2957_);
lean_ctor_set_uint8(v_reuseFailAlloc_3094_, sizeof(void*)*12 + 4, v_heqProofs_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3094_, sizeof(void*)*12 + 5, v_funCC_2963_);
v___x_2993_ = v_reuseFailAlloc_3094_;
goto v_reusejp_2992_;
}
v___jp_2969_:
{
uint8_t v___x_2970_; 
v___x_2970_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_2949_, v_lhs_2927_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2972_; 
lean_del_object(v___x_2946_);
lean_dec(v_snd_2939_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v_next_2949_);
lean_ctor_set(v___x_2941_, 0, v___x_2968_);
v___x_2972_ = v___x_2941_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_next_2949_);
v___x_2972_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
v_a_2930_ = v___x_2972_;
goto _start;
}
}
else
{
lean_object* v___x_2975_; lean_object* v___x_2977_; 
lean_dec_ref(v_next_2949_);
lean_dec_ref(v_rootNew_2928_);
v___x_2975_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v___x_2975_);
v___x_2977_ = v___x_2941_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_snd_2939_);
v___x_2977_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2979_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v___x_2977_);
v___x_2979_ = v___x_2946_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
v___jp_2982_:
{
if (lean_obj_tag(v___y_2983_) == 0)
{
lean_dec_ref_known(v___y_2983_, 1);
goto v___jp_2969_;
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v_next_2949_);
lean_del_object(v___x_2946_);
lean_del_object(v___x_2941_);
lean_dec(v_snd_2939_);
lean_dec_ref(v_rootNew_2928_);
v_a_2984_ = lean_ctor_get(v___y_2983_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___y_2983_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___y_2983_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___y_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
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
lean_inc_ref(v_self_2948_);
v___x_2994_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2948_, v___x_2993_, v___y_2931_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_dec_ref_known(v___x_2994_, 1);
if (v_a_2929_ == 0)
{
lean_dec_ref(v___x_2993_);
lean_dec(v_ematchDiagSource_2964_);
lean_dec(v_sTerms_2962_);
lean_dec(v_mt_2961_);
lean_dec(v_generation_2960_);
lean_dec(v_idx_2959_);
lean_dec(v_size_2954_);
lean_dec(v_proof_x3f_2952_);
lean_dec(v_target_x3f_2951_);
lean_dec_ref(v_self_2948_);
goto v___jp_2969_;
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2995_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2996_ = lean_unsigned_to_nat(3u);
v___x_2997_ = l_Lean_Expr_isAppOfArity(v_self_2948_, v___x_2995_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_dec_ref(v___x_2993_);
lean_dec(v_ematchDiagSource_2964_);
lean_dec(v_sTerms_2962_);
lean_dec(v_mt_2961_);
lean_dec(v_generation_2960_);
lean_dec(v_idx_2959_);
lean_dec(v_size_2954_);
lean_dec(v_proof_x3f_2952_);
lean_dec(v_target_x3f_2951_);
lean_dec_ref(v_self_2948_);
goto v___jp_2969_;
}
else
{
uint8_t v___x_2998_; 
v___x_2998_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2993_);
lean_dec_ref(v___x_2993_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; lean_object* v_toGoalState_3000_; lean_object* v_enodeMap_3001_; lean_object* v_congrTable_3002_; lean_object* v___x_3003_; 
v___x_2999_ = lean_st_ref_get(v___y_2931_);
v_toGoalState_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_toGoalState_3000_);
lean_dec(v___x_2999_);
v_enodeMap_3001_ = lean_ctor_get(v_toGoalState_3000_, 1);
lean_inc_ref(v_enodeMap_3001_);
v_congrTable_3002_ = lean_ctor_get(v_toGoalState_3000_, 4);
lean_inc_ref(v_congrTable_3002_);
lean_dec_ref(v_toGoalState_3000_);
lean_inc_ref(v_self_2948_);
v___x_3003_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3001_, v_congrTable_3002_, v_self_2948_);
lean_dec_ref(v_congrTable_3002_);
lean_dec_ref(v_enodeMap_3001_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_dec(v_ematchDiagSource_2964_);
lean_dec(v_sTerms_2962_);
lean_dec(v_mt_2961_);
lean_dec(v_generation_2960_);
lean_dec(v_idx_2959_);
lean_dec(v_size_2954_);
lean_dec(v_proof_x3f_2952_);
lean_dec(v_target_x3f_2951_);
lean_dec_ref(v_self_2948_);
goto v___jp_2969_;
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
v___x_3006_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3005_, v___y_2932_);
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
lean_object* v___x_3009_; lean_object* v_toGoalState_3010_; lean_object* v_mvarId_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3085_; 
v___x_3009_ = lean_st_ref_take(v___y_2931_);
v_toGoalState_3010_ = lean_ctor_get(v___x_3009_, 0);
v_mvarId_3011_ = lean_ctor_get(v___x_3009_, 1);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3013_ = v___x_3009_;
v_isShared_3014_ = v_isSharedCheck_3085_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_mvarId_3011_);
lean_inc(v_toGoalState_3010_);
lean_dec(v___x_3009_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3085_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v_nextDeclIdx_3015_; lean_object* v_enodeMap_3016_; lean_object* v_exprs_3017_; lean_object* v_parents_3018_; lean_object* v_congrTable_3019_; lean_object* v_appMap_3020_; lean_object* v_indicesFound_3021_; lean_object* v_newFacts_3022_; uint8_t v_inconsistent_3023_; lean_object* v_nextIdx_3024_; lean_object* v_newRawFacts_3025_; lean_object* v_facts_3026_; lean_object* v_extThms_3027_; lean_object* v_ematch_3028_; lean_object* v_inj_3029_; lean_object* v_split_3030_; lean_object* v_clean_3031_; lean_object* v_sstates_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3084_; 
v_nextDeclIdx_3015_ = lean_ctor_get(v_toGoalState_3010_, 0);
v_enodeMap_3016_ = lean_ctor_get(v_toGoalState_3010_, 1);
v_exprs_3017_ = lean_ctor_get(v_toGoalState_3010_, 2);
v_parents_3018_ = lean_ctor_get(v_toGoalState_3010_, 3);
v_congrTable_3019_ = lean_ctor_get(v_toGoalState_3010_, 4);
v_appMap_3020_ = lean_ctor_get(v_toGoalState_3010_, 5);
v_indicesFound_3021_ = lean_ctor_get(v_toGoalState_3010_, 6);
v_newFacts_3022_ = lean_ctor_get(v_toGoalState_3010_, 7);
v_inconsistent_3023_ = lean_ctor_get_uint8(v_toGoalState_3010_, sizeof(void*)*17);
v_nextIdx_3024_ = lean_ctor_get(v_toGoalState_3010_, 8);
v_newRawFacts_3025_ = lean_ctor_get(v_toGoalState_3010_, 9);
v_facts_3026_ = lean_ctor_get(v_toGoalState_3010_, 10);
v_extThms_3027_ = lean_ctor_get(v_toGoalState_3010_, 11);
v_ematch_3028_ = lean_ctor_get(v_toGoalState_3010_, 12);
v_inj_3029_ = lean_ctor_get(v_toGoalState_3010_, 13);
v_split_3030_ = lean_ctor_get(v_toGoalState_3010_, 14);
v_clean_3031_ = lean_ctor_get(v_toGoalState_3010_, 15);
v_sstates_3032_ = lean_ctor_get(v_toGoalState_3010_, 16);
v_isSharedCheck_3084_ = !lean_is_exclusive(v_toGoalState_3010_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3034_ = v_toGoalState_3010_;
v_isShared_3035_ = v_isSharedCheck_3084_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_sstates_3032_);
lean_inc(v_clean_3031_);
lean_inc(v_split_3030_);
lean_inc(v_inj_3029_);
lean_inc(v_ematch_3028_);
lean_inc(v_extThms_3027_);
lean_inc(v_facts_3026_);
lean_inc(v_newRawFacts_3025_);
lean_inc(v_nextIdx_3024_);
lean_inc(v_newFacts_3022_);
lean_inc(v_indicesFound_3021_);
lean_inc(v_appMap_3020_);
lean_inc(v_congrTable_3019_);
lean_inc(v_parents_3018_);
lean_inc(v_exprs_3017_);
lean_inc(v_enodeMap_3016_);
lean_inc(v_nextDeclIdx_3015_);
lean_dec(v_toGoalState_3010_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3084_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3036_ = lean_box(0);
lean_inc_ref(v_self_2948_);
v___x_3037_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3016_, v_congrTable_3019_, v_self_2948_, v___x_3036_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 4, v___x_3037_);
v___x_3039_ = v___x_3034_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_nextDeclIdx_3015_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_enodeMap_3016_);
lean_ctor_set(v_reuseFailAlloc_3083_, 2, v_exprs_3017_);
lean_ctor_set(v_reuseFailAlloc_3083_, 3, v_parents_3018_);
lean_ctor_set(v_reuseFailAlloc_3083_, 4, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3083_, 5, v_appMap_3020_);
lean_ctor_set(v_reuseFailAlloc_3083_, 6, v_indicesFound_3021_);
lean_ctor_set(v_reuseFailAlloc_3083_, 7, v_newFacts_3022_);
lean_ctor_set(v_reuseFailAlloc_3083_, 8, v_nextIdx_3024_);
lean_ctor_set(v_reuseFailAlloc_3083_, 9, v_newRawFacts_3025_);
lean_ctor_set(v_reuseFailAlloc_3083_, 10, v_facts_3026_);
lean_ctor_set(v_reuseFailAlloc_3083_, 11, v_extThms_3027_);
lean_ctor_set(v_reuseFailAlloc_3083_, 12, v_ematch_3028_);
lean_ctor_set(v_reuseFailAlloc_3083_, 13, v_inj_3029_);
lean_ctor_set(v_reuseFailAlloc_3083_, 14, v_split_3030_);
lean_ctor_set(v_reuseFailAlloc_3083_, 15, v_clean_3031_);
lean_ctor_set(v_reuseFailAlloc_3083_, 16, v_sstates_3032_);
lean_ctor_set_uint8(v_reuseFailAlloc_3083_, sizeof(void*)*17, v_inconsistent_3023_);
v___x_3039_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3041_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3039_);
v___x_3041_ = v___x_3013_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_mvarId_3011_);
v___x_3041_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = lean_st_ref_set(v___y_2931_, v___x_3041_);
lean_inc_ref(v_rootNew_2928_);
lean_inc_ref(v_next_2949_);
lean_inc_ref_n(v_self_2948_, 3);
v___x_3043_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3043_, 0, v_self_2948_);
lean_ctor_set(v___x_3043_, 1, v_next_2949_);
lean_ctor_set(v___x_3043_, 2, v_rootNew_2928_);
lean_ctor_set(v___x_3043_, 3, v_self_2948_);
lean_ctor_set(v___x_3043_, 4, v_target_x3f_2951_);
lean_ctor_set(v___x_3043_, 5, v_proof_x3f_2952_);
lean_ctor_set(v___x_3043_, 6, v_size_2954_);
lean_ctor_set(v___x_3043_, 7, v_idx_2959_);
lean_ctor_set(v___x_3043_, 8, v_generation_2960_);
lean_ctor_set(v___x_3043_, 9, v_mt_2961_);
lean_ctor_set(v___x_3043_, 10, v_sTerms_2962_);
lean_ctor_set(v___x_3043_, 11, v_ematchDiagSource_2964_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*12, v_flipped_2953_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*12 + 1, v_interpreted_2955_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*12 + 2, v_ctor_2956_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*12 + 3, v_hasLambdas_2957_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*12 + 4, v_heqProofs_2958_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*12 + 5, v_funCC_2963_);
v___x_3044_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2948_, v___x_3043_, v___y_2931_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec_ref_known(v___x_3044_, 1);
v___x_3045_ = lean_st_ref_get(v___y_2931_);
lean_inc(v_fst_3005_);
v___x_3046_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3045_, v_fst_3005_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___x_3045_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v_self_3048_; lean_object* v_next_3049_; lean_object* v_root_3050_; lean_object* v_target_x3f_3051_; lean_object* v_proof_x3f_3052_; uint8_t v_flipped_3053_; lean_object* v_size_3054_; uint8_t v_interpreted_3055_; uint8_t v_ctor_3056_; uint8_t v_hasLambdas_3057_; uint8_t v_heqProofs_3058_; lean_object* v_idx_3059_; lean_object* v_generation_3060_; lean_object* v_mt_3061_; lean_object* v_sTerms_3062_; uint8_t v_funCC_3063_; lean_object* v_ematchDiagSource_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3072_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3046_, 1);
v_self_3048_ = lean_ctor_get(v_a_3047_, 0);
v_next_3049_ = lean_ctor_get(v_a_3047_, 1);
v_root_3050_ = lean_ctor_get(v_a_3047_, 2);
v_target_x3f_3051_ = lean_ctor_get(v_a_3047_, 4);
v_proof_x3f_3052_ = lean_ctor_get(v_a_3047_, 5);
v_flipped_3053_ = lean_ctor_get_uint8(v_a_3047_, sizeof(void*)*12);
v_size_3054_ = lean_ctor_get(v_a_3047_, 6);
v_interpreted_3055_ = lean_ctor_get_uint8(v_a_3047_, sizeof(void*)*12 + 1);
v_ctor_3056_ = lean_ctor_get_uint8(v_a_3047_, sizeof(void*)*12 + 2);
v_hasLambdas_3057_ = lean_ctor_get_uint8(v_a_3047_, sizeof(void*)*12 + 3);
v_heqProofs_3058_ = lean_ctor_get_uint8(v_a_3047_, sizeof(void*)*12 + 4);
v_idx_3059_ = lean_ctor_get(v_a_3047_, 7);
v_generation_3060_ = lean_ctor_get(v_a_3047_, 8);
v_mt_3061_ = lean_ctor_get(v_a_3047_, 9);
v_sTerms_3062_ = lean_ctor_get(v_a_3047_, 10);
v_funCC_3063_ = lean_ctor_get_uint8(v_a_3047_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3064_ = lean_ctor_get(v_a_3047_, 11);
v_isSharedCheck_3072_ = !lean_is_exclusive(v_a_3047_);
if (v_isSharedCheck_3072_ == 0)
{
lean_object* v_unused_3073_; 
v_unused_3073_ = lean_ctor_get(v_a_3047_, 3);
lean_dec(v_unused_3073_);
v___x_3066_ = v_a_3047_;
v_isShared_3067_ = v_isSharedCheck_3072_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_ematchDiagSource_3064_);
lean_inc(v_sTerms_3062_);
lean_inc(v_mt_3061_);
lean_inc(v_generation_3060_);
lean_inc(v_idx_3059_);
lean_inc(v_size_3054_);
lean_inc(v_proof_x3f_3052_);
lean_inc(v_target_x3f_3051_);
lean_inc(v_root_3050_);
lean_inc(v_next_3049_);
lean_inc(v_self_3048_);
lean_dec(v_a_3047_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3072_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 3, v_self_2948_);
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_self_3048_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v_next_3049_);
lean_ctor_set(v_reuseFailAlloc_3071_, 2, v_root_3050_);
lean_ctor_set(v_reuseFailAlloc_3071_, 3, v_self_2948_);
lean_ctor_set(v_reuseFailAlloc_3071_, 4, v_target_x3f_3051_);
lean_ctor_set(v_reuseFailAlloc_3071_, 5, v_proof_x3f_3052_);
lean_ctor_set(v_reuseFailAlloc_3071_, 6, v_size_3054_);
lean_ctor_set(v_reuseFailAlloc_3071_, 7, v_idx_3059_);
lean_ctor_set(v_reuseFailAlloc_3071_, 8, v_generation_3060_);
lean_ctor_set(v_reuseFailAlloc_3071_, 9, v_mt_3061_);
lean_ctor_set(v_reuseFailAlloc_3071_, 10, v_sTerms_3062_);
lean_ctor_set(v_reuseFailAlloc_3071_, 11, v_ematchDiagSource_3064_);
lean_ctor_set_uint8(v_reuseFailAlloc_3071_, sizeof(void*)*12, v_flipped_3053_);
lean_ctor_set_uint8(v_reuseFailAlloc_3071_, sizeof(void*)*12 + 1, v_interpreted_3055_);
lean_ctor_set_uint8(v_reuseFailAlloc_3071_, sizeof(void*)*12 + 2, v_ctor_3056_);
lean_ctor_set_uint8(v_reuseFailAlloc_3071_, sizeof(void*)*12 + 3, v_hasLambdas_3057_);
lean_ctor_set_uint8(v_reuseFailAlloc_3071_, sizeof(void*)*12 + 4, v_heqProofs_3058_);
lean_ctor_set_uint8(v_reuseFailAlloc_3071_, sizeof(void*)*12 + 5, v_funCC_3063_);
v___x_3069_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3005_, v___x_3069_, v___y_2931_);
v___y_2983_ = v___x_3070_;
goto v___jp_2982_;
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_fst_3005_);
lean_dec_ref(v_next_2949_);
lean_dec_ref(v_self_2948_);
lean_del_object(v___x_2946_);
lean_del_object(v___x_2941_);
lean_dec(v_snd_2939_);
lean_dec_ref(v_rootNew_2928_);
v_a_3074_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3046_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3046_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_dec(v_fst_3005_);
lean_dec_ref(v_self_2948_);
v___y_2983_ = v___x_3044_;
goto v___jp_2982_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3005_);
lean_dec(v_ematchDiagSource_2964_);
lean_dec(v_sTerms_2962_);
lean_dec(v_mt_2961_);
lean_dec(v_generation_2960_);
lean_dec(v_idx_2959_);
lean_dec(v_size_2954_);
lean_dec(v_proof_x3f_2952_);
lean_dec(v_target_x3f_2951_);
lean_dec_ref(v_self_2948_);
goto v___jp_2969_;
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_fst_3005_);
lean_dec(v_ematchDiagSource_2964_);
lean_dec(v_sTerms_2962_);
lean_dec(v_mt_2961_);
lean_dec(v_generation_2960_);
lean_dec(v_idx_2959_);
lean_dec(v_size_2954_);
lean_dec(v_proof_x3f_2952_);
lean_dec(v_target_x3f_2951_);
lean_dec_ref(v_next_2949_);
lean_dec_ref(v_self_2948_);
lean_del_object(v___x_2946_);
lean_del_object(v___x_2941_);
lean_dec(v_snd_2939_);
lean_dec_ref(v_rootNew_2928_);
v_a_3086_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3006_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3006_);
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
else
{
lean_dec(v_ematchDiagSource_2964_);
lean_dec(v_sTerms_2962_);
lean_dec(v_mt_2961_);
lean_dec(v_generation_2960_);
lean_dec(v_idx_2959_);
lean_dec(v_size_2954_);
lean_dec(v_proof_x3f_2952_);
lean_dec(v_target_x3f_2951_);
lean_dec_ref(v_self_2948_);
goto v___jp_2969_;
}
}
}
}
else
{
lean_dec_ref(v___x_2993_);
lean_dec(v_ematchDiagSource_2964_);
lean_dec(v_sTerms_2962_);
lean_dec(v_mt_2961_);
lean_dec(v_generation_2960_);
lean_dec(v_idx_2959_);
lean_dec(v_size_2954_);
lean_dec(v_proof_x3f_2952_);
lean_dec(v_target_x3f_2951_);
lean_dec_ref(v_self_2948_);
v___y_2983_ = v___x_2994_;
goto v___jp_2982_;
}
}
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_del_object(v___x_2941_);
lean_dec(v_snd_2939_);
lean_dec_ref(v_rootNew_2928_);
v_a_3098_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_2943_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_2943_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3108_, lean_object* v_rootNew_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
uint8_t v_a_27974__boxed_3119_; lean_object* v_res_3120_; 
v_a_27974__boxed_3119_ = lean_unbox(v_a_3110_);
v_res_3120_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3108_, v_rootNew_3109_, v_a_27974__boxed_3119_, v_a_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v_lhs_3108_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3121_, lean_object* v_rootNew_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3122_, v_a_3127_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; lean_object* v___x_3139_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref_known(v___x_3134_, 1);
v___x_3136_ = lean_box(0);
lean_inc_ref(v_lhs_3121_);
v___x_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
lean_ctor_set(v___x_3137_, 1, v_lhs_3121_);
v___x_3138_ = lean_unbox(v_a_3135_);
lean_dec(v_a_3135_);
v___x_3139_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3121_, v_rootNew_3122_, v___x_3138_, v___x_3137_, v_a_3123_, v_a_3127_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_);
lean_dec_ref(v_lhs_3121_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3153_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3153_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3153_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v_fst_3144_; 
v_fst_3144_ = lean_ctor_get(v_a_3140_, 0);
lean_inc(v_fst_3144_);
lean_dec(v_a_3140_);
if (lean_obj_tag(v_fst_3144_) == 0)
{
lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3145_ = lean_box(0);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3145_);
v___x_3147_ = v___x_3142_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
else
{
lean_object* v_val_3149_; lean_object* v___x_3151_; 
v_val_3149_ = lean_ctor_get(v_fst_3144_, 0);
lean_inc(v_val_3149_);
lean_dec_ref_known(v_fst_3144_, 1);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v_val_3149_);
v___x_3151_ = v___x_3142_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_val_3149_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v_a_3154_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3139_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3139_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec_ref(v_rootNew_3122_);
lean_dec_ref(v_lhs_3121_);
v_a_3162_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3134_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3134_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3170_, lean_object* v_rootNew_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3170_, v_rootNew_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_);
lean_dec(v_a_3181_);
lean_dec_ref(v_a_3180_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
lean_dec(v_a_3173_);
lean_dec(v_a_3172_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3184_, lean_object* v_00_u03b2_3185_, lean_object* v_x_3186_, lean_object* v_x_3187_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3184_, v_x_3186_, v_x_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3189_, lean_object* v_00_u03b2_3190_, lean_object* v_x_3191_, lean_object* v_x_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3189_, v_00_u03b2_3190_, v_x_3191_, v_x_3192_);
lean_dec_ref(v_x_3191_);
lean_dec_ref(v___x_3189_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3194_, lean_object* v_00_u03b2_3195_, lean_object* v_x_3196_, lean_object* v_x_3197_, lean_object* v_x_3198_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3194_, v_x_3196_, v_x_3197_, v_x_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3200_, lean_object* v_00_u03b2_3201_, lean_object* v_x_3202_, lean_object* v_x_3203_, lean_object* v_x_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3200_, v_00_u03b2_3201_, v_x_3202_, v_x_3203_, v_x_3204_);
lean_dec_ref(v___x_3200_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3206_, lean_object* v_rootNew_3207_, uint8_t v_a_3208_, lean_object* v_inst_3209_, lean_object* v_a_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3206_, v_rootNew_3207_, v_a_3208_, v_a_3210_, v___y_3211_, v___y_3215_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3223_, lean_object* v_rootNew_3224_, lean_object* v_a_3225_, lean_object* v_inst_3226_, lean_object* v_a_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
uint8_t v_a_28329__boxed_3239_; lean_object* v_res_3240_; 
v_a_28329__boxed_3239_ = lean_unbox(v_a_3225_);
v_res_3240_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3223_, v_rootNew_3224_, v_a_28329__boxed_3239_, v_inst_3226_, v_a_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v_lhs_3223_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3241_, lean_object* v_00_u03b2_3242_, lean_object* v_x_3243_, size_t v_x_3244_, lean_object* v_x_3245_){
_start:
{
lean_object* v___x_3246_; 
lean_inc_ref(v_x_3243_);
v___x_3246_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3241_, v_x_3243_, v_x_3244_, v_x_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3247_, lean_object* v_00_u03b2_3248_, lean_object* v_x_3249_, lean_object* v_x_3250_, lean_object* v_x_3251_){
_start:
{
size_t v_x_28372__boxed_3252_; lean_object* v_res_3253_; 
v_x_28372__boxed_3252_ = lean_unbox_usize(v_x_3250_);
lean_dec(v_x_3250_);
v_res_3253_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3247_, v_00_u03b2_3248_, v_x_3249_, v_x_28372__boxed_3252_, v_x_3251_);
lean_dec_ref(v_x_3249_);
lean_dec_ref(v___x_3247_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3254_, lean_object* v_00_u03b2_3255_, lean_object* v_x_3256_, size_t v_x_3257_, size_t v_x_3258_, lean_object* v_x_3259_, lean_object* v_x_3260_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3254_, v_x_3256_, v_x_3257_, v_x_3258_, v_x_3259_, v_x_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3262_, lean_object* v_00_u03b2_3263_, lean_object* v_x_3264_, lean_object* v_x_3265_, lean_object* v_x_3266_, lean_object* v_x_3267_, lean_object* v_x_3268_){
_start:
{
size_t v_x_28386__boxed_3269_; size_t v_x_28387__boxed_3270_; lean_object* v_res_3271_; 
v_x_28386__boxed_3269_ = lean_unbox_usize(v_x_3265_);
lean_dec(v_x_3265_);
v_x_28387__boxed_3270_ = lean_unbox_usize(v_x_3266_);
lean_dec(v_x_3266_);
v_res_3271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3262_, v_00_u03b2_3263_, v_x_3264_, v_x_28386__boxed_3269_, v_x_28387__boxed_3270_, v_x_3267_, v_x_3268_);
lean_dec_ref(v___x_3262_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3272_, lean_object* v_00_u03b2_3273_, lean_object* v_keys_3274_, lean_object* v_vals_3275_, lean_object* v_heq_3276_, lean_object* v_i_3277_, lean_object* v_k_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3272_, v_keys_3274_, v_vals_3275_, v_i_3277_, v_k_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3280_, lean_object* v_00_u03b2_3281_, lean_object* v_keys_3282_, lean_object* v_vals_3283_, lean_object* v_heq_3284_, lean_object* v_i_3285_, lean_object* v_k_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3280_, v_00_u03b2_3281_, v_keys_3282_, v_vals_3283_, v_heq_3284_, v_i_3285_, v_k_3286_);
lean_dec_ref(v_vals_3283_);
lean_dec_ref(v_keys_3282_);
lean_dec_ref(v___x_3280_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3288_, lean_object* v_00_u03b2_3289_, lean_object* v_n_3290_, lean_object* v_k_3291_, lean_object* v_v_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3288_, v_n_3290_, v_k_3291_, v_v_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3294_, lean_object* v_00_u03b2_3295_, lean_object* v_n_3296_, lean_object* v_k_3297_, lean_object* v_v_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3294_, v_00_u03b2_3295_, v_n_3296_, v_k_3297_, v_v_3298_);
lean_dec_ref(v___x_3294_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3300_, lean_object* v_00_u03b2_3301_, size_t v_depth_3302_, lean_object* v_keys_3303_, lean_object* v_vals_3304_, lean_object* v_heq_3305_, lean_object* v_i_3306_, lean_object* v_entries_3307_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3300_, v_depth_3302_, v_keys_3303_, v_vals_3304_, v_i_3306_, v_entries_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3309_, lean_object* v_00_u03b2_3310_, lean_object* v_depth_3311_, lean_object* v_keys_3312_, lean_object* v_vals_3313_, lean_object* v_heq_3314_, lean_object* v_i_3315_, lean_object* v_entries_3316_){
_start:
{
size_t v_depth_boxed_3317_; lean_object* v_res_3318_; 
v_depth_boxed_3317_ = lean_unbox_usize(v_depth_3311_);
lean_dec(v_depth_3311_);
v_res_3318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3309_, v_00_u03b2_3310_, v_depth_boxed_3317_, v_keys_3312_, v_vals_3313_, v_heq_3314_, v_i_3315_, v_entries_3316_);
lean_dec_ref(v_vals_3313_);
lean_dec_ref(v_keys_3312_);
lean_dec_ref(v___x_3309_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3319_, lean_object* v_00_u03b2_3320_, lean_object* v_x_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_, lean_object* v_x_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3319_, v_x_3321_, v_x_3322_, v_x_3323_, v_x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3326_, lean_object* v_00_u03b2_3327_, lean_object* v_x_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_, lean_object* v_x_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3326_, v_00_u03b2_3327_, v_x_3328_, v_x_3329_, v_x_3330_, v_x_3331_);
lean_dec_ref(v___x_3326_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3333_, lean_object* v_b_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
if (lean_obj_tag(v_as_x27_3333_) == 0)
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_b_3334_);
return v___x_3346_;
}
else
{
lean_object* v_head_3347_; lean_object* v_tail_3348_; lean_object* v___x_3349_; 
v_head_3347_ = lean_ctor_get(v_as_x27_3333_, 0);
v_tail_3348_ = lean_ctor_get(v_as_x27_3333_, 1);
lean_inc(v_head_3347_);
v___x_3349_ = l_Lean_Meta_Grind_propagateUp(v_head_3347_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v___x_3350_; 
lean_dec_ref_known(v___x_3349_, 1);
v___x_3350_ = lean_box(0);
v_as_x27_3333_ = v_tail_3348_;
v_b_3334_ = v___x_3350_;
goto _start;
}
else
{
return v___x_3349_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3352_, lean_object* v_b_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3352_, v_b_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v_as_x27_3352_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3366_, lean_object* v_b_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
if (lean_obj_tag(v_as_x27_3366_) == 0)
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v_b_3367_);
return v___x_3379_;
}
else
{
lean_object* v_head_3380_; lean_object* v_tail_3381_; lean_object* v___x_3382_; 
v_head_3380_ = lean_ctor_get(v_as_x27_3366_, 0);
v_tail_3381_ = lean_ctor_get(v_as_x27_3366_, 1);
lean_inc(v_head_3380_);
v___x_3382_ = l_Lean_Meta_Grind_propagateDown(v_head_3380_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v___x_3383_; 
lean_dec_ref_known(v___x_3382_, 1);
v___x_3383_ = lean_box(0);
v_as_x27_3366_ = v_tail_3381_;
v_b_3367_ = v___x_3383_;
goto _start;
}
else
{
return v___x_3382_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3385_, lean_object* v_b_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3385_, v_b_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec(v_as_x27_3385_);
return v_res_3398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v_cls_3402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3403_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3404_ = l_Lean_Name_append(v___x_3403_, v_cls_3402_);
return v___x_3404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
return v___x_3410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3413_ = l_Lean_stringToMessageData(v___x_3412_);
return v___x_3413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3416_ = l_Lean_stringToMessageData(v___x_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3417_, uint8_t v_isHEq_3418_, lean_object* v_lhs_3419_, lean_object* v_rhs_3420_, lean_object* v_lhsNode_3421_, lean_object* v_rhsNode_3422_, lean_object* v_lhsRoot_3423_, lean_object* v_rhsRoot_3424_, uint8_t v_flipped_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; uint8_t v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; uint8_t v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; uint8_t v___y_3514_; lean_object* v___y_3515_; uint8_t v___y_3516_; uint8_t v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; uint8_t v___y_3525_; uint8_t v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; uint8_t v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; uint8_t v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; uint8_t v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; uint8_t v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; uint8_t v___y_3591_; uint8_t v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; uint8_t v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v_options_3675_; lean_object* v_inheritedTraceOptions_3676_; uint8_t v_hasTrace_3677_; lean_object* v_cls_3678_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v_fns_u2082_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v_fns_u2081_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; 
v_options_3675_ = lean_ctor_get(v_a_3434_, 2);
v_inheritedTraceOptions_3676_ = lean_ctor_get(v_a_3434_, 13);
v_hasTrace_3677_ = lean_ctor_get_uint8(v_options_3675_, sizeof(void*)*1);
v_cls_3678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3677_ == 0)
{
v___y_3797_ = v_a_3426_;
v___y_3798_ = v_a_3427_;
v___y_3799_ = v_a_3428_;
v___y_3800_ = v_a_3429_;
v___y_3801_ = v_a_3430_;
v___y_3802_ = v_a_3431_;
v___y_3803_ = v_a_3432_;
v___y_3804_ = v_a_3433_;
v___y_3805_ = v_a_3434_;
v___y_3806_ = v_a_3435_;
goto v___jp_3796_;
}
else
{
lean_object* v___x_3877_; uint8_t v___x_3878_; 
v___x_3877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3878_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3676_, v_options_3675_, v___x_3877_);
if (v___x_3878_ == 0)
{
v___y_3797_ = v_a_3426_;
v___y_3798_ = v_a_3427_;
v___y_3799_ = v_a_3428_;
v___y_3800_ = v_a_3429_;
v___y_3801_ = v_a_3430_;
v___y_3802_ = v_a_3431_;
v___y_3803_ = v_a_3432_;
v___y_3804_ = v_a_3433_;
v___y_3805_ = v_a_3434_;
v___y_3806_ = v_a_3435_;
goto v___jp_3796_;
}
else
{
lean_object* v___x_3879_; 
v___x_3879_ = l_Lean_Meta_Grind_updateLastTag(v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v___x_3880_; 
lean_dec_ref_known(v___x_3879_, 1);
lean_inc_ref(v_lhs_3419_);
v___x_3880_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3419_, v_a_3426_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3882_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
lean_inc_ref(v_rhs_3420_);
v___x_3882_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3420_, v_a_3426_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
v___x_3884_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
lean_ctor_set(v___x_3885_, 1, v_a_3881_);
v___x_3886_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3885_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
lean_ctor_set(v___x_3888_, 1, v_a_3883_);
v___x_3889_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3678_, v___x_3888_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_dec_ref_known(v___x_3889_, 1);
v___y_3797_ = v_a_3426_;
v___y_3798_ = v_a_3427_;
v___y_3799_ = v_a_3428_;
v___y_3800_ = v_a_3429_;
v___y_3801_ = v_a_3430_;
v___y_3802_ = v_a_3431_;
v___y_3803_ = v_a_3432_;
v___y_3804_ = v_a_3433_;
v___y_3805_ = v_a_3434_;
v___y_3806_ = v_a_3435_;
goto v___jp_3796_;
}
else
{
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhsNode_3421_);
lean_dec_ref(v_rhs_3420_);
lean_dec_ref(v_lhs_3419_);
lean_dec_ref(v_proof_3417_);
return v___x_3889_;
}
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
lean_dec(v_a_3881_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhsNode_3421_);
lean_dec_ref(v_rhs_3420_);
lean_dec_ref(v_lhs_3419_);
lean_dec_ref(v_proof_3417_);
v_a_3890_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3882_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3882_);
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
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhsNode_3421_);
lean_dec_ref(v_rhs_3420_);
lean_dec_ref(v_lhs_3419_);
lean_dec_ref(v_proof_3417_);
v_a_3898_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3880_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3880_);
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
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhsNode_3421_);
lean_dec_ref(v_rhs_3420_);
lean_dec_ref(v_lhs_3419_);
lean_dec_ref(v_proof_3417_);
return v___x_3879_;
}
}
}
v___jp_3437_:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3444_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3480_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3480_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3480_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
uint8_t v___x_3459_; 
v___x_3459_ = lean_unbox(v_a_3455_);
lean_dec(v_a_3455_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
lean_del_object(v___x_3457_);
v___x_3460_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3443_);
lean_dec(v___y_3443_);
v___x_3461_ = lean_box(0);
v___x_3462_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3460_, v___x_3461_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___x_3460_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v___x_3463_; 
lean_dec_ref_known(v___x_3462_, 1);
v___x_3463_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3439_, v___x_3461_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v___x_3464_; 
lean_dec_ref_known(v___x_3463_, 1);
v___x_3464_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3440_, v___y_3442_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v___y_3440_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v___x_3465_; 
lean_dec_ref_known(v___x_3464_, 1);
v___x_3465_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3438_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3474_; 
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3474_ == 0)
{
lean_object* v_unused_3475_; 
v_unused_3475_ = lean_ctor_get(v___x_3465_, 0);
lean_dec(v_unused_3475_);
v___x_3467_ = v___x_3465_;
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
else
{
lean_dec(v___x_3465_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
uint8_t v___x_3469_; 
v___x_3469_ = l_Lean_Expr_isTrue(v___y_3441_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3471_; 
lean_dec(v___y_3439_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3461_);
v___x_3471_ = v___x_3467_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3461_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
else
{
lean_object* v___x_3473_; 
lean_del_object(v___x_3467_);
v___x_3473_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3439_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3439_);
return v___x_3473_;
}
}
}
else
{
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3439_);
return v___x_3465_;
}
}
else
{
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
return v___x_3464_;
}
}
else
{
lean_dec_ref(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
return v___x_3463_;
}
}
else
{
lean_dec_ref(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
return v___x_3462_;
}
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
v___x_3476_ = lean_box(0);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3476_);
v___x_3478_ = v___x_3457_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3439_);
lean_dec(v___y_3438_);
v_a_3481_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3454_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3454_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
v___jp_3489_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
lean_inc_ref(v___y_3506_);
v___x_3526_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3526_, 0, v___y_3506_);
lean_ctor_set(v___x_3526_, 1, v___y_3507_);
lean_ctor_set(v___x_3526_, 2, v___y_3502_);
lean_ctor_set(v___x_3526_, 3, v___y_3522_);
lean_ctor_set(v___x_3526_, 4, v___y_3491_);
lean_ctor_set(v___x_3526_, 5, v___y_3503_);
lean_ctor_set(v___x_3526_, 6, v___y_3495_);
lean_ctor_set(v___x_3526_, 7, v___y_3492_);
lean_ctor_set(v___x_3526_, 8, v___y_3515_);
lean_ctor_set(v___x_3526_, 9, v___y_3520_);
lean_ctor_set(v___x_3526_, 10, v___y_3494_);
lean_ctor_set(v___x_3526_, 11, v___y_3497_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*12, v___y_3517_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*12 + 1, v___y_3490_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*12 + 2, v___y_3514_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*12 + 3, v___y_3516_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*12 + 4, v___y_3525_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*12 + 5, v___y_3493_);
lean_inc_ref(v___y_3508_);
v___x_3527_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3508_, v___x_3526_, v___y_3498_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v___x_3528_; 
lean_dec_ref_known(v___x_3527_, 1);
lean_inc_ref(v___y_3519_);
v___x_3528_ = l_Lean_Meta_Grind_propagateBeta(v___y_3519_, v___y_3523_, v___y_3498_, v___y_3521_, v___y_3518_, v___y_3513_, v___y_3496_, v___y_3512_, v___y_3500_, v___y_3505_, v___y_3501_, v___y_3510_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v___x_3529_; 
lean_dec_ref_known(v___x_3528_, 1);
lean_inc_ref(v___y_3509_);
v___x_3529_ = l_Lean_Meta_Grind_propagateBeta(v___y_3509_, v___y_3524_, v___y_3498_, v___y_3521_, v___y_3518_, v___y_3513_, v___y_3496_, v___y_3512_, v___y_3500_, v___y_3505_, v___y_3501_, v___y_3510_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v___x_3530_; 
lean_dec_ref_known(v___x_3529_, 1);
v___x_3530_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3424_, v_lhsRoot_3423_, v___y_3498_, v___y_3500_, v___y_3505_, v___y_3501_, v___y_3510_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3532_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v___x_3532_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3511_, v___y_3498_);
lean_dec_ref(v___y_3511_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v___x_3533_; 
lean_dec_ref_known(v___x_3532_, 1);
lean_inc_ref(v___y_3508_);
v___x_3533_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3504_, v___y_3508_, v___y_3498_, v___y_3521_, v___y_3518_, v___y_3513_, v___y_3496_, v___y_3512_, v___y_3500_, v___y_3505_, v___y_3501_, v___y_3510_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v___x_3534_; 
lean_dec_ref_known(v___x_3533_, 1);
v___x_3534_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3498_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; uint8_t v___x_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
v___x_3536_ = lean_unbox(v_a_3535_);
lean_dec(v_a_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
v___x_3537_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3506_, v___y_3498_, v___y_3521_, v___y_3518_, v___y_3513_, v___y_3496_, v___y_3512_, v___y_3500_, v___y_3505_, v___y_3501_, v___y_3510_);
lean_dec_ref(v___y_3506_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_dec_ref_known(v___x_3537_, 1);
v___y_3438_ = v_a_3531_;
v___y_3439_ = v___y_3499_;
v___y_3440_ = v___y_3519_;
v___y_3441_ = v___y_3508_;
v___y_3442_ = v___y_3509_;
v___y_3443_ = v___y_3504_;
v___y_3444_ = v___y_3498_;
v___y_3445_ = v___y_3521_;
v___y_3446_ = v___y_3518_;
v___y_3447_ = v___y_3513_;
v___y_3448_ = v___y_3496_;
v___y_3449_ = v___y_3512_;
v___y_3450_ = v___y_3500_;
v___y_3451_ = v___y_3505_;
v___y_3452_ = v___y_3501_;
v___y_3453_ = v___y_3510_;
goto v___jp_3437_;
}
else
{
lean_dec(v_a_3531_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec(v___y_3499_);
return v___x_3537_;
}
}
else
{
lean_dec_ref(v___y_3506_);
v___y_3438_ = v_a_3531_;
v___y_3439_ = v___y_3499_;
v___y_3440_ = v___y_3519_;
v___y_3441_ = v___y_3508_;
v___y_3442_ = v___y_3509_;
v___y_3443_ = v___y_3504_;
v___y_3444_ = v___y_3498_;
v___y_3445_ = v___y_3521_;
v___y_3446_ = v___y_3518_;
v___y_3447_ = v___y_3513_;
v___y_3448_ = v___y_3496_;
v___y_3449_ = v___y_3512_;
v___y_3450_ = v___y_3500_;
v___y_3451_ = v___y_3505_;
v___y_3452_ = v___y_3501_;
v___y_3453_ = v___y_3510_;
goto v___jp_3437_;
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec(v_a_3531_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3504_);
lean_dec(v___y_3499_);
v_a_3538_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3534_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3534_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_dec(v_a_3531_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3504_);
lean_dec(v___y_3499_);
return v___x_3533_;
}
}
else
{
lean_dec(v_a_3531_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3504_);
lean_dec(v___y_3499_);
return v___x_3532_;
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3504_);
lean_dec(v___y_3499_);
v_a_3546_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3530_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3530_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
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
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3504_);
lean_dec(v___y_3499_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
return v___x_3529_;
}
}
else
{
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3504_);
lean_dec(v___y_3499_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
return v___x_3528_;
}
}
else
{
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3504_);
lean_dec(v___y_3499_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
return v___x_3527_;
}
}
v___jp_3554_:
{
if (v_isHEq_3418_ == 0)
{
if (v___y_3572_ == 0)
{
v___y_3490_ = v___y_3555_;
v___y_3491_ = v___y_3556_;
v___y_3492_ = v___y_3557_;
v___y_3493_ = v___y_3558_;
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3561_;
v___y_3497_ = v___y_3562_;
v___y_3498_ = v___y_3564_;
v___y_3499_ = v___y_3566_;
v___y_3500_ = v___y_3565_;
v___y_3501_ = v___y_3567_;
v___y_3502_ = v___y_3568_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3570_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3574_;
v___y_3508_ = v___y_3575_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3577_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3591_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3583_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3589_;
v___y_3523_ = v___y_3588_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3563_;
goto v___jp_3489_;
}
else
{
v___y_3490_ = v___y_3555_;
v___y_3491_ = v___y_3556_;
v___y_3492_ = v___y_3557_;
v___y_3493_ = v___y_3558_;
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3561_;
v___y_3497_ = v___y_3562_;
v___y_3498_ = v___y_3564_;
v___y_3499_ = v___y_3566_;
v___y_3500_ = v___y_3565_;
v___y_3501_ = v___y_3567_;
v___y_3502_ = v___y_3568_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3570_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3574_;
v___y_3508_ = v___y_3575_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3577_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3591_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3583_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3589_;
v___y_3523_ = v___y_3588_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3572_;
goto v___jp_3489_;
}
}
else
{
v___y_3490_ = v___y_3555_;
v___y_3491_ = v___y_3556_;
v___y_3492_ = v___y_3557_;
v___y_3493_ = v___y_3558_;
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3561_;
v___y_3497_ = v___y_3562_;
v___y_3498_ = v___y_3564_;
v___y_3499_ = v___y_3566_;
v___y_3500_ = v___y_3565_;
v___y_3501_ = v___y_3567_;
v___y_3502_ = v___y_3568_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3570_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3574_;
v___y_3508_ = v___y_3575_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3577_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3591_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3583_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3587_;
v___y_3522_ = v___y_3589_;
v___y_3523_ = v___y_3588_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v_isHEq_3418_;
goto v___jp_3489_;
}
}
v___jp_3592_:
{
lean_object* v___x_3615_; 
v___x_3615_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_dec_ref_known(v___x_3615_, 1);
v___x_3616_ = lean_st_ref_get(v___y_3605_);
v___x_3617_ = lean_st_ref_get(v___y_3605_);
lean_inc_ref(v___y_3594_);
v___x_3618_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3617_, v___y_3594_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___x_3617_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v_self_3620_; lean_object* v_root_3621_; lean_object* v_congr_3622_; lean_object* v_target_x3f_3623_; lean_object* v_proof_x3f_3624_; uint8_t v_flipped_3625_; lean_object* v_size_3626_; uint8_t v_interpreted_3627_; uint8_t v_ctor_3628_; uint8_t v_hasLambdas_3629_; uint8_t v_heqProofs_3630_; lean_object* v_idx_3631_; lean_object* v_generation_3632_; lean_object* v_mt_3633_; lean_object* v_sTerms_3634_; uint8_t v_funCC_3635_; lean_object* v_ematchDiagSource_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3665_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v_self_3620_ = lean_ctor_get(v_a_3619_, 0);
v_root_3621_ = lean_ctor_get(v_a_3619_, 2);
v_congr_3622_ = lean_ctor_get(v_a_3619_, 3);
v_target_x3f_3623_ = lean_ctor_get(v_a_3619_, 4);
v_proof_x3f_3624_ = lean_ctor_get(v_a_3619_, 5);
v_flipped_3625_ = lean_ctor_get_uint8(v_a_3619_, sizeof(void*)*12);
v_size_3626_ = lean_ctor_get(v_a_3619_, 6);
v_interpreted_3627_ = lean_ctor_get_uint8(v_a_3619_, sizeof(void*)*12 + 1);
v_ctor_3628_ = lean_ctor_get_uint8(v_a_3619_, sizeof(void*)*12 + 2);
v_hasLambdas_3629_ = lean_ctor_get_uint8(v_a_3619_, sizeof(void*)*12 + 3);
v_heqProofs_3630_ = lean_ctor_get_uint8(v_a_3619_, sizeof(void*)*12 + 4);
v_idx_3631_ = lean_ctor_get(v_a_3619_, 7);
v_generation_3632_ = lean_ctor_get(v_a_3619_, 8);
v_mt_3633_ = lean_ctor_get(v_a_3619_, 9);
v_sTerms_3634_ = lean_ctor_get(v_a_3619_, 10);
v_funCC_3635_ = lean_ctor_get_uint8(v_a_3619_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3636_ = lean_ctor_get(v_a_3619_, 11);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_a_3619_);
if (v_isSharedCheck_3665_ == 0)
{
lean_object* v_unused_3666_; 
v_unused_3666_ = lean_ctor_get(v_a_3619_, 1);
lean_dec(v_unused_3666_);
v___x_3638_ = v_a_3619_;
v_isShared_3639_ = v_isSharedCheck_3665_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_ematchDiagSource_3636_);
lean_inc(v_sTerms_3634_);
lean_inc(v_mt_3633_);
lean_inc(v_generation_3632_);
lean_inc(v_idx_3631_);
lean_inc(v_size_3626_);
lean_inc(v_proof_x3f_3624_);
lean_inc(v_target_x3f_3623_);
lean_inc(v_congr_3622_);
lean_inc(v_root_3621_);
lean_inc(v_self_3620_);
lean_dec(v_a_3619_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3665_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v_self_3640_; lean_object* v_next_3641_; lean_object* v_root_3642_; lean_object* v_congr_3643_; lean_object* v_target_x3f_3644_; lean_object* v_proof_x3f_3645_; uint8_t v_flipped_3646_; lean_object* v_size_3647_; uint8_t v_interpreted_3648_; uint8_t v_ctor_3649_; uint8_t v_hasLambdas_3650_; uint8_t v_heqProofs_3651_; lean_object* v_idx_3652_; lean_object* v_generation_3653_; lean_object* v_mt_3654_; lean_object* v_sTerms_3655_; uint8_t v_funCC_3656_; lean_object* v_ematchDiagSource_3657_; lean_object* v___x_3659_; 
v_self_3640_ = lean_ctor_get(v_rhsRoot_3424_, 0);
v_next_3641_ = lean_ctor_get(v_rhsRoot_3424_, 1);
v_root_3642_ = lean_ctor_get(v_rhsRoot_3424_, 2);
v_congr_3643_ = lean_ctor_get(v_rhsRoot_3424_, 3);
v_target_x3f_3644_ = lean_ctor_get(v_rhsRoot_3424_, 4);
v_proof_x3f_3645_ = lean_ctor_get(v_rhsRoot_3424_, 5);
v_flipped_3646_ = lean_ctor_get_uint8(v_rhsRoot_3424_, sizeof(void*)*12);
v_size_3647_ = lean_ctor_get(v_rhsRoot_3424_, 6);
v_interpreted_3648_ = lean_ctor_get_uint8(v_rhsRoot_3424_, sizeof(void*)*12 + 1);
v_ctor_3649_ = lean_ctor_get_uint8(v_rhsRoot_3424_, sizeof(void*)*12 + 2);
v_hasLambdas_3650_ = lean_ctor_get_uint8(v_rhsRoot_3424_, sizeof(void*)*12 + 3);
v_heqProofs_3651_ = lean_ctor_get_uint8(v_rhsRoot_3424_, sizeof(void*)*12 + 4);
v_idx_3652_ = lean_ctor_get(v_rhsRoot_3424_, 7);
v_generation_3653_ = lean_ctor_get(v_rhsRoot_3424_, 8);
v_mt_3654_ = lean_ctor_get(v_rhsRoot_3424_, 9);
v_sTerms_3655_ = lean_ctor_get(v_rhsRoot_3424_, 10);
v_funCC_3656_ = lean_ctor_get_uint8(v_rhsRoot_3424_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3657_ = lean_ctor_get(v_rhsRoot_3424_, 11);
lean_inc_ref(v_next_3641_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 1, v_next_3641_);
v___x_3659_ = v___x_3638_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_self_3620_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_next_3641_);
lean_ctor_set(v_reuseFailAlloc_3664_, 2, v_root_3621_);
lean_ctor_set(v_reuseFailAlloc_3664_, 3, v_congr_3622_);
lean_ctor_set(v_reuseFailAlloc_3664_, 4, v_target_x3f_3623_);
lean_ctor_set(v_reuseFailAlloc_3664_, 5, v_proof_x3f_3624_);
lean_ctor_set(v_reuseFailAlloc_3664_, 6, v_size_3626_);
lean_ctor_set(v_reuseFailAlloc_3664_, 7, v_idx_3631_);
lean_ctor_set(v_reuseFailAlloc_3664_, 8, v_generation_3632_);
lean_ctor_set(v_reuseFailAlloc_3664_, 9, v_mt_3633_);
lean_ctor_set(v_reuseFailAlloc_3664_, 10, v_sTerms_3634_);
lean_ctor_set(v_reuseFailAlloc_3664_, 11, v_ematchDiagSource_3636_);
lean_ctor_set_uint8(v_reuseFailAlloc_3664_, sizeof(void*)*12, v_flipped_3625_);
lean_ctor_set_uint8(v_reuseFailAlloc_3664_, sizeof(void*)*12 + 1, v_interpreted_3627_);
lean_ctor_set_uint8(v_reuseFailAlloc_3664_, sizeof(void*)*12 + 2, v_ctor_3628_);
lean_ctor_set_uint8(v_reuseFailAlloc_3664_, sizeof(void*)*12 + 3, v_hasLambdas_3629_);
lean_ctor_set_uint8(v_reuseFailAlloc_3664_, sizeof(void*)*12 + 4, v_heqProofs_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3664_, sizeof(void*)*12 + 5, v_funCC_3635_);
v___x_3659_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3603_, v___x_3659_, v___y_3605_);
if (lean_obj_tag(v___x_3660_) == 0)
{
uint8_t v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
lean_dec_ref_known(v___x_3660_, 1);
v___x_3661_ = 0;
v___x_3662_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3616_, v_lhs_3419_, v___x_3661_);
lean_dec(v___x_3616_);
v___x_3663_ = lean_nat_add(v_size_3647_, v___y_3595_);
lean_dec(v___y_3595_);
if (v_hasLambdas_3650_ == 0)
{
lean_inc_ref(v_congr_3643_);
lean_inc(v_mt_3654_);
lean_inc(v_generation_3653_);
lean_inc_ref(v_self_3640_);
lean_inc(v_proof_x3f_3645_);
lean_inc_ref(v_root_3642_);
lean_inc(v_ematchDiagSource_3657_);
lean_inc(v_sTerms_3655_);
lean_inc(v_idx_3652_);
lean_inc(v_target_x3f_3644_);
v___y_3555_ = v_interpreted_3648_;
v___y_3556_ = v_target_x3f_3644_;
v___y_3557_ = v_idx_3652_;
v___y_3558_ = v_funCC_3656_;
v___y_3559_ = v_sTerms_3655_;
v___y_3560_ = v___x_3663_;
v___y_3561_ = v___y_3609_;
v___y_3562_ = v_ematchDiagSource_3657_;
v___y_3563_ = v___y_3593_;
v___y_3564_ = v___y_3605_;
v___y_3565_ = v___y_3611_;
v___y_3566_ = v___x_3662_;
v___y_3567_ = v___y_3613_;
v___y_3568_ = v_root_3642_;
v___y_3569_ = v_proof_x3f_3645_;
v___y_3570_ = v___y_3604_;
v___y_3571_ = v___y_3612_;
v___y_3572_ = v_heqProofs_3651_;
v___y_3573_ = v_self_3640_;
v___y_3574_ = v___y_3598_;
v___y_3575_ = v___y_3597_;
v___y_3576_ = v___y_3599_;
v___y_3577_ = v___y_3614_;
v___y_3578_ = v___y_3594_;
v___y_3579_ = v___y_3610_;
v___y_3580_ = v___y_3608_;
v___y_3581_ = v_ctor_3649_;
v___y_3582_ = v_generation_3653_;
v___y_3583_ = v___y_3607_;
v___y_3584_ = v_flipped_3646_;
v___y_3585_ = v___y_3596_;
v___y_3586_ = v_mt_3654_;
v___y_3587_ = v___y_3606_;
v___y_3588_ = v___y_3600_;
v___y_3589_ = v_congr_3643_;
v___y_3590_ = v___y_3601_;
v___y_3591_ = v___y_3602_;
goto v___jp_3554_;
}
else
{
lean_inc_ref(v_congr_3643_);
lean_inc(v_mt_3654_);
lean_inc(v_generation_3653_);
lean_inc_ref(v_self_3640_);
lean_inc(v_proof_x3f_3645_);
lean_inc_ref(v_root_3642_);
lean_inc(v_ematchDiagSource_3657_);
lean_inc(v_sTerms_3655_);
lean_inc(v_idx_3652_);
lean_inc(v_target_x3f_3644_);
v___y_3555_ = v_interpreted_3648_;
v___y_3556_ = v_target_x3f_3644_;
v___y_3557_ = v_idx_3652_;
v___y_3558_ = v_funCC_3656_;
v___y_3559_ = v_sTerms_3655_;
v___y_3560_ = v___x_3663_;
v___y_3561_ = v___y_3609_;
v___y_3562_ = v_ematchDiagSource_3657_;
v___y_3563_ = v___y_3593_;
v___y_3564_ = v___y_3605_;
v___y_3565_ = v___y_3611_;
v___y_3566_ = v___x_3662_;
v___y_3567_ = v___y_3613_;
v___y_3568_ = v_root_3642_;
v___y_3569_ = v_proof_x3f_3645_;
v___y_3570_ = v___y_3604_;
v___y_3571_ = v___y_3612_;
v___y_3572_ = v_heqProofs_3651_;
v___y_3573_ = v_self_3640_;
v___y_3574_ = v___y_3598_;
v___y_3575_ = v___y_3597_;
v___y_3576_ = v___y_3599_;
v___y_3577_ = v___y_3614_;
v___y_3578_ = v___y_3594_;
v___y_3579_ = v___y_3610_;
v___y_3580_ = v___y_3608_;
v___y_3581_ = v_ctor_3649_;
v___y_3582_ = v_generation_3653_;
v___y_3583_ = v___y_3607_;
v___y_3584_ = v_flipped_3646_;
v___y_3585_ = v___y_3596_;
v___y_3586_ = v_mt_3654_;
v___y_3587_ = v___y_3606_;
v___y_3588_ = v___y_3600_;
v___y_3589_ = v_congr_3643_;
v___y_3590_ = v___y_3601_;
v___y_3591_ = v_hasLambdas_3650_;
goto v___jp_3554_;
}
}
else
{
lean_dec(v___x_3616_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_lhs_3419_);
return v___x_3660_;
}
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_dec(v___x_3616_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_lhs_3419_);
v_a_3667_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3618_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3618_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
else
{
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_lhs_3419_);
return v___x_3615_;
}
}
v___jp_3679_:
{
lean_object* v_self_3695_; lean_object* v_next_3696_; lean_object* v_size_3697_; uint8_t v_hasLambdas_3698_; uint8_t v_heqProofs_3699_; lean_object* v___x_3700_; 
v_self_3695_ = lean_ctor_get(v_lhsRoot_3423_, 0);
v_next_3696_ = lean_ctor_get(v_lhsRoot_3423_, 1);
v_size_3697_ = lean_ctor_get(v_lhsRoot_3423_, 6);
v_hasLambdas_3698_ = lean_ctor_get_uint8(v_lhsRoot_3423_, sizeof(void*)*12 + 3);
v_heqProofs_3699_ = lean_ctor_get_uint8(v_lhsRoot_3423_, sizeof(void*)*12 + 4);
v___x_3700_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3695_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v_root_3702_; lean_object* v___x_3703_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v_root_3702_ = lean_ctor_get(v_rhsNode_3422_, 2);
lean_inc_ref_n(v_root_3702_, 2);
lean_dec_ref(v_rhsNode_3422_);
lean_inc_ref(v_lhs_3419_);
v___x_3703_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3419_, v_root_3702_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_options_3704_; uint8_t v_hasTrace_3705_; 
lean_dec_ref_known(v___x_3703_, 1);
v_options_3704_ = lean_ctor_get(v___y_3693_, 2);
v_hasTrace_3705_ = lean_ctor_get_uint8(v_options_3704_, sizeof(void*)*1);
if (v_hasTrace_3705_ == 0)
{
lean_inc_ref(v_next_3696_);
lean_inc(v_size_3697_);
lean_inc_ref(v_self_3695_);
v___y_3593_ = v_heqProofs_3699_;
v___y_3594_ = v_self_3695_;
v___y_3595_ = v_size_3697_;
v___y_3596_ = v___y_3680_;
v___y_3597_ = v_root_3702_;
v___y_3598_ = v_next_3696_;
v___y_3599_ = v___y_3681_;
v___y_3600_ = v___y_3682_;
v___y_3601_ = v_fns_u2082_3684_;
v___y_3602_ = v_hasLambdas_3698_;
v___y_3603_ = v___y_3683_;
v___y_3604_ = v_a_3701_;
v___y_3605_ = v___y_3685_;
v___y_3606_ = v___y_3686_;
v___y_3607_ = v___y_3687_;
v___y_3608_ = v___y_3688_;
v___y_3609_ = v___y_3689_;
v___y_3610_ = v___y_3690_;
v___y_3611_ = v___y_3691_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v___y_3693_;
v___y_3614_ = v___y_3694_;
goto v___jp_3592_;
}
else
{
lean_object* v_inheritedTraceOptions_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v_inheritedTraceOptions_3706_ = lean_ctor_get(v___y_3693_, 13);
v___x_3707_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3708_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3706_, v_options_3704_, v___x_3707_);
if (v___x_3708_ == 0)
{
lean_inc_ref(v_next_3696_);
lean_inc(v_size_3697_);
lean_inc_ref(v_self_3695_);
v___y_3593_ = v_heqProofs_3699_;
v___y_3594_ = v_self_3695_;
v___y_3595_ = v_size_3697_;
v___y_3596_ = v___y_3680_;
v___y_3597_ = v_root_3702_;
v___y_3598_ = v_next_3696_;
v___y_3599_ = v___y_3681_;
v___y_3600_ = v___y_3682_;
v___y_3601_ = v_fns_u2082_3684_;
v___y_3602_ = v_hasLambdas_3698_;
v___y_3603_ = v___y_3683_;
v___y_3604_ = v_a_3701_;
v___y_3605_ = v___y_3685_;
v___y_3606_ = v___y_3686_;
v___y_3607_ = v___y_3687_;
v___y_3608_ = v___y_3688_;
v___y_3609_ = v___y_3689_;
v___y_3610_ = v___y_3690_;
v___y_3611_ = v___y_3691_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v___y_3693_;
v___y_3614_ = v___y_3694_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Lean_Meta_Grind_updateLastTag(v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v___x_3710_; 
lean_dec_ref_known(v___x_3709_, 1);
lean_inc_ref(v_lhs_3419_);
v___x_3710_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3419_, v___y_3685_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3712_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
lean_inc_ref(v_root_3702_);
v___x_3712_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3702_, v___y_3685_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
v___x_3714_ = lean_st_ref_get(v___y_3685_);
lean_inc_ref(v_lhs_3419_);
v___x_3715_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3714_, v_lhs_3419_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec(v___x_3714_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3716_, v___y_3685_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3719_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3720_, 0, v_a_3711_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
lean_ctor_set(v___x_3721_, 1, v_a_3713_);
v___x_3722_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
lean_ctor_set(v___x_3724_, 1, v_a_3718_);
v___x_3725_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3678_, v___x_3724_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_dec_ref_known(v___x_3725_, 1);
lean_inc_ref(v_next_3696_);
lean_inc(v_size_3697_);
lean_inc_ref(v_self_3695_);
v___y_3593_ = v_heqProofs_3699_;
v___y_3594_ = v_self_3695_;
v___y_3595_ = v_size_3697_;
v___y_3596_ = v___y_3680_;
v___y_3597_ = v_root_3702_;
v___y_3598_ = v_next_3696_;
v___y_3599_ = v___y_3681_;
v___y_3600_ = v___y_3682_;
v___y_3601_ = v_fns_u2082_3684_;
v___y_3602_ = v_hasLambdas_3698_;
v___y_3603_ = v___y_3683_;
v___y_3604_ = v_a_3701_;
v___y_3605_ = v___y_3685_;
v___y_3606_ = v___y_3686_;
v___y_3607_ = v___y_3687_;
v___y_3608_ = v___y_3688_;
v___y_3609_ = v___y_3689_;
v___y_3610_ = v___y_3690_;
v___y_3611_ = v___y_3691_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v___y_3693_;
v___y_3614_ = v___y_3694_;
goto v___jp_3592_;
}
else
{
lean_dec_ref(v_root_3702_);
lean_dec(v_a_3701_);
lean_dec_ref(v_fns_u2082_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_lhs_3419_);
return v___x_3725_;
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_dec(v_a_3713_);
lean_dec(v_a_3711_);
lean_dec_ref(v_root_3702_);
lean_dec(v_a_3701_);
lean_dec_ref(v_fns_u2082_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_lhs_3419_);
v_a_3726_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3717_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3717_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec(v_a_3713_);
lean_dec(v_a_3711_);
lean_dec_ref(v_root_3702_);
lean_dec(v_a_3701_);
lean_dec_ref(v_fns_u2082_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_lhs_3419_);
v_a_3734_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3715_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3715_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec(v_a_3711_);
lean_dec_ref(v_root_3702_);
lean_dec(v_a_3701_);
lean_dec_ref(v_fns_u2082_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_lhs_3419_);
v_a_3742_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3712_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3712_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec_ref(v_root_3702_);
lean_dec(v_a_3701_);
lean_dec_ref(v_fns_u2082_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_lhs_3419_);
v_a_3750_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3710_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3710_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
else
{
lean_dec_ref(v_root_3702_);
lean_dec(v_a_3701_);
lean_dec_ref(v_fns_u2082_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_lhs_3419_);
return v___x_3709_;
}
}
}
}
else
{
lean_dec_ref(v_root_3702_);
lean_dec(v_a_3701_);
lean_dec_ref(v_fns_u2082_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_lhs_3419_);
return v___x_3703_;
}
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
lean_dec_ref(v_fns_u2082_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhs_3419_);
v_a_3758_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3700_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3700_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
v___jp_3766_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3781_ = lean_array_get_size(v___y_3768_);
v___x_3782_ = lean_unsigned_to_nat(0u);
v___x_3783_ = lean_nat_dec_eq(v___x_3781_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v_self_3784_; lean_object* v___x_3785_; 
v_self_3784_ = lean_ctor_get(v_lhsRoot_3423_, 0);
lean_inc_ref(v_self_3784_);
v___x_3785_ = l_Lean_Meta_Grind_getFnRoots(v_self_3784_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___y_3680_ = v___y_3767_;
v___y_3681_ = v___y_3768_;
v___y_3682_ = v_fns_u2081_3770_;
v___y_3683_ = v___y_3769_;
v_fns_u2082_3684_ = v_a_3786_;
v___y_3685_ = v___y_3771_;
v___y_3686_ = v___y_3772_;
v___y_3687_ = v___y_3773_;
v___y_3688_ = v___y_3774_;
v___y_3689_ = v___y_3775_;
v___y_3690_ = v___y_3776_;
v___y_3691_ = v___y_3777_;
v___y_3692_ = v___y_3778_;
v___y_3693_ = v___y_3779_;
v___y_3694_ = v___y_3780_;
goto v___jp_3679_;
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v_fns_u2081_3770_);
lean_dec_ref(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhs_3419_);
v_a_3787_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3785_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3785_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_object* v___x_3795_; 
v___x_3795_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3680_ = v___y_3767_;
v___y_3681_ = v___y_3768_;
v___y_3682_ = v_fns_u2081_3770_;
v___y_3683_ = v___y_3769_;
v_fns_u2082_3684_ = v___x_3795_;
v___y_3685_ = v___y_3771_;
v___y_3686_ = v___y_3772_;
v___y_3687_ = v___y_3773_;
v___y_3688_ = v___y_3774_;
v___y_3689_ = v___y_3775_;
v___y_3690_ = v___y_3776_;
v___y_3691_ = v___y_3777_;
v___y_3692_ = v___y_3778_;
v___y_3693_ = v___y_3779_;
v___y_3694_ = v___y_3780_;
goto v___jp_3679_;
}
}
v___jp_3796_:
{
lean_object* v___x_3807_; 
lean_inc_ref(v_lhs_3419_);
v___x_3807_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3419_, v___y_3797_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3875_; 
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3875_ == 0)
{
lean_object* v_unused_3876_; 
v_unused_3876_ = lean_ctor_get(v___x_3807_, 0);
lean_dec(v_unused_3876_);
v___x_3809_ = v___x_3807_;
v_isShared_3810_ = v_isSharedCheck_3875_;
goto v_resetjp_3808_;
}
else
{
lean_dec(v___x_3807_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3875_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v_self_3811_; lean_object* v_next_3812_; lean_object* v_root_3813_; lean_object* v_congr_3814_; lean_object* v_size_3815_; uint8_t v_interpreted_3816_; uint8_t v_ctor_3817_; uint8_t v_hasLambdas_3818_; uint8_t v_heqProofs_3819_; lean_object* v_idx_3820_; lean_object* v_generation_3821_; lean_object* v_mt_3822_; lean_object* v_sTerms_3823_; uint8_t v_funCC_3824_; lean_object* v_ematchDiagSource_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3872_; 
v_self_3811_ = lean_ctor_get(v_lhsNode_3421_, 0);
v_next_3812_ = lean_ctor_get(v_lhsNode_3421_, 1);
v_root_3813_ = lean_ctor_get(v_lhsNode_3421_, 2);
v_congr_3814_ = lean_ctor_get(v_lhsNode_3421_, 3);
v_size_3815_ = lean_ctor_get(v_lhsNode_3421_, 6);
v_interpreted_3816_ = lean_ctor_get_uint8(v_lhsNode_3421_, sizeof(void*)*12 + 1);
v_ctor_3817_ = lean_ctor_get_uint8(v_lhsNode_3421_, sizeof(void*)*12 + 2);
v_hasLambdas_3818_ = lean_ctor_get_uint8(v_lhsNode_3421_, sizeof(void*)*12 + 3);
v_heqProofs_3819_ = lean_ctor_get_uint8(v_lhsNode_3421_, sizeof(void*)*12 + 4);
v_idx_3820_ = lean_ctor_get(v_lhsNode_3421_, 7);
v_generation_3821_ = lean_ctor_get(v_lhsNode_3421_, 8);
v_mt_3822_ = lean_ctor_get(v_lhsNode_3421_, 9);
v_sTerms_3823_ = lean_ctor_get(v_lhsNode_3421_, 10);
v_funCC_3824_ = lean_ctor_get_uint8(v_lhsNode_3421_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3825_ = lean_ctor_get(v_lhsNode_3421_, 11);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_lhsNode_3421_);
if (v_isSharedCheck_3872_ == 0)
{
lean_object* v_unused_3873_; lean_object* v_unused_3874_; 
v_unused_3873_ = lean_ctor_get(v_lhsNode_3421_, 5);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_lhsNode_3421_, 4);
lean_dec(v_unused_3874_);
v___x_3827_ = v_lhsNode_3421_;
v_isShared_3828_ = v_isSharedCheck_3872_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_ematchDiagSource_3825_);
lean_inc(v_sTerms_3823_);
lean_inc(v_mt_3822_);
lean_inc(v_generation_3821_);
lean_inc(v_idx_3820_);
lean_inc(v_size_3815_);
lean_inc(v_congr_3814_);
lean_inc(v_root_3813_);
lean_inc(v_next_3812_);
lean_inc(v_self_3811_);
lean_dec(v_lhsNode_3421_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3872_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3810_ == 0)
{
lean_ctor_set_tag(v___x_3809_, 1);
lean_ctor_set(v___x_3809_, 0, v_rhs_3420_);
v___x_3830_ = v___x_3809_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_rhs_3420_);
v___x_3830_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3831_, 0, v_proof_3417_);
lean_inc_ref(v_root_3813_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 5, v___x_3831_);
lean_ctor_set(v___x_3827_, 4, v___x_3830_);
v___x_3833_ = v___x_3827_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_self_3811_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_next_3812_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v_root_3813_);
lean_ctor_set(v_reuseFailAlloc_3870_, 3, v_congr_3814_);
lean_ctor_set(v_reuseFailAlloc_3870_, 4, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3870_, 5, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3870_, 6, v_size_3815_);
lean_ctor_set(v_reuseFailAlloc_3870_, 7, v_idx_3820_);
lean_ctor_set(v_reuseFailAlloc_3870_, 8, v_generation_3821_);
lean_ctor_set(v_reuseFailAlloc_3870_, 9, v_mt_3822_);
lean_ctor_set(v_reuseFailAlloc_3870_, 10, v_sTerms_3823_);
lean_ctor_set(v_reuseFailAlloc_3870_, 11, v_ematchDiagSource_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3870_, sizeof(void*)*12 + 1, v_interpreted_3816_);
lean_ctor_set_uint8(v_reuseFailAlloc_3870_, sizeof(void*)*12 + 2, v_ctor_3817_);
lean_ctor_set_uint8(v_reuseFailAlloc_3870_, sizeof(void*)*12 + 3, v_hasLambdas_3818_);
lean_ctor_set_uint8(v_reuseFailAlloc_3870_, sizeof(void*)*12 + 4, v_heqProofs_3819_);
lean_ctor_set_uint8(v_reuseFailAlloc_3870_, sizeof(void*)*12 + 5, v_funCC_3824_);
v___x_3833_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; 
lean_ctor_set_uint8(v___x_3833_, sizeof(void*)*12, v_flipped_3425_);
lean_inc_ref(v_lhs_3419_);
v___x_3834_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3419_, v___x_3833_, v___y_3797_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v___x_3835_; 
lean_dec_ref_known(v___x_3834_, 1);
v___x_3835_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3423_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3837_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref_known(v___x_3835_, 1);
v___x_3837_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3424_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3837_, 1);
v___x_3839_ = lean_array_get_size(v_a_3836_);
v___x_3840_ = lean_unsigned_to_nat(0u);
v___x_3841_ = lean_nat_dec_eq(v___x_3839_, v___x_3840_);
if (v___x_3841_ == 0)
{
lean_object* v_self_3842_; lean_object* v___x_3843_; 
v_self_3842_ = lean_ctor_get(v_rhsRoot_3424_, 0);
lean_inc_ref(v_self_3842_);
v___x_3843_ = l_Lean_Meta_Grind_getFnRoots(v_self_3842_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref_known(v___x_3843_, 1);
v___y_3767_ = v_a_3836_;
v___y_3768_ = v_a_3838_;
v___y_3769_ = v_root_3813_;
v_fns_u2081_3770_ = v_a_3844_;
v___y_3771_ = v___y_3797_;
v___y_3772_ = v___y_3798_;
v___y_3773_ = v___y_3799_;
v___y_3774_ = v___y_3800_;
v___y_3775_ = v___y_3801_;
v___y_3776_ = v___y_3802_;
v___y_3777_ = v___y_3803_;
v___y_3778_ = v___y_3804_;
v___y_3779_ = v___y_3805_;
v___y_3780_ = v___y_3806_;
goto v___jp_3766_;
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec(v_a_3838_);
lean_dec(v_a_3836_);
lean_dec_ref(v_root_3813_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhs_3419_);
v_a_3845_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3843_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3843_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
lean_object* v___x_3853_; 
v___x_3853_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3767_ = v_a_3836_;
v___y_3768_ = v_a_3838_;
v___y_3769_ = v_root_3813_;
v_fns_u2081_3770_ = v___x_3853_;
v___y_3771_ = v___y_3797_;
v___y_3772_ = v___y_3798_;
v___y_3773_ = v___y_3799_;
v___y_3774_ = v___y_3800_;
v___y_3775_ = v___y_3801_;
v___y_3776_ = v___y_3802_;
v___y_3777_ = v___y_3803_;
v___y_3778_ = v___y_3804_;
v___y_3779_ = v___y_3805_;
v___y_3780_ = v___y_3806_;
goto v___jp_3766_;
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v_a_3836_);
lean_dec_ref(v_root_3813_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhs_3419_);
v_a_3854_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3837_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3837_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec_ref(v_root_3813_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhs_3419_);
v_a_3862_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3835_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3835_);
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
lean_dec_ref(v_root_3813_);
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhs_3419_);
return v___x_3834_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3424_);
lean_dec_ref(v_lhsRoot_3423_);
lean_dec_ref(v_rhsNode_3422_);
lean_dec_ref(v_lhsNode_3421_);
lean_dec_ref(v_rhs_3420_);
lean_dec_ref(v_lhs_3419_);
lean_dec_ref(v_proof_3417_);
return v___x_3807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3906_ = _args[0];
lean_object* v_isHEq_3907_ = _args[1];
lean_object* v_lhs_3908_ = _args[2];
lean_object* v_rhs_3909_ = _args[3];
lean_object* v_lhsNode_3910_ = _args[4];
lean_object* v_rhsNode_3911_ = _args[5];
lean_object* v_lhsRoot_3912_ = _args[6];
lean_object* v_rhsRoot_3913_ = _args[7];
lean_object* v_flipped_3914_ = _args[8];
lean_object* v_a_3915_ = _args[9];
lean_object* v_a_3916_ = _args[10];
lean_object* v_a_3917_ = _args[11];
lean_object* v_a_3918_ = _args[12];
lean_object* v_a_3919_ = _args[13];
lean_object* v_a_3920_ = _args[14];
lean_object* v_a_3921_ = _args[15];
lean_object* v_a_3922_ = _args[16];
lean_object* v_a_3923_ = _args[17];
lean_object* v_a_3924_ = _args[18];
lean_object* v_a_3925_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3926_; uint8_t v_flipped_boxed_3927_; lean_object* v_res_3928_; 
v_isHEq_boxed_3926_ = lean_unbox(v_isHEq_3907_);
v_flipped_boxed_3927_ = lean_unbox(v_flipped_3914_);
v_res_3928_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3906_, v_isHEq_boxed_3926_, v_lhs_3908_, v_rhs_3909_, v_lhsNode_3910_, v_rhsNode_3911_, v_lhsRoot_3912_, v_rhsRoot_3913_, v_flipped_boxed_3927_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
lean_dec(v_a_3918_);
lean_dec_ref(v_a_3917_);
lean_dec(v_a_3916_);
lean_dec(v_a_3915_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3929_, lean_object* v_as_x27_3930_, lean_object* v_b_3931_, lean_object* v_a_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3930_, v_b_3931_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3945_, lean_object* v_as_x27_3946_, lean_object* v_b_3947_, lean_object* v_a_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3945_, v_as_x27_3946_, v_b_3947_, v_a_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec(v_as_x27_3946_);
lean_dec(v_as_3945_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3961_, lean_object* v_as_x27_3962_, lean_object* v_b_3963_, lean_object* v_a_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3962_, v_b_3963_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3977_, lean_object* v_as_x27_3978_, lean_object* v_b_3979_, lean_object* v_a_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3977_, v_as_x27_3978_, v_b_3979_, v_a_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec(v_as_x27_3978_);
lean_dec(v_as_3977_);
return v_res_3992_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_3995_ = l_Lean_stringToMessageData(v___x_3994_);
return v___x_3995_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4001_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4002_ = l_Lean_Name_append(v___x_4001_, v___x_4000_);
return v___x_4002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4005_ = l_Lean_stringToMessageData(v___x_4004_);
return v___x_4005_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4008_ = l_Lean_stringToMessageData(v___x_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4009_, lean_object* v_rhs_4010_, lean_object* v_proof_4011_, uint8_t v_isHEq_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4027_ = lean_st_ref_get(v_a_4013_);
lean_inc_ref(v_lhs_4009_);
v___x_4028_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4027_, v_lhs_4009_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
lean_dec(v___x_4027_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref_known(v___x_4028_, 1);
v___x_4030_ = lean_st_ref_get(v_a_4013_);
lean_inc_ref(v_rhs_4010_);
v___x_4031_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4030_, v_rhs_4010_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
lean_dec(v___x_4030_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v_root_4033_; lean_object* v_root_4034_; uint8_t v___x_4035_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v_root_4033_ = lean_ctor_get(v_a_4029_, 2);
v_root_4034_ = lean_ctor_get(v_a_4032_, 2);
v___x_4035_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_4033_, v_root_4034_);
if (v___x_4035_ == 0)
{
lean_object* v_options_4036_; lean_object* v_inheritedTraceOptions_4037_; uint8_t v_hasTrace_4038_; uint8_t v___x_4039_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4076_; lean_object* v___y_4077_; uint8_t v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4104_; lean_object* v___y_4105_; uint8_t v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; uint8_t v___y_4117_; lean_object* v___y_4122_; lean_object* v___y_4123_; uint8_t v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4149_; lean_object* v___y_4150_; uint8_t v___y_4151_; uint8_t v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; uint8_t v___y_4169_; lean_object* v___y_4170_; uint8_t v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; uint8_t v___y_4185_; lean_object* v___y_4186_; uint8_t v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; uint8_t v___y_4201_; lean_object* v___y_4202_; uint8_t v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; uint8_t v___y_4211_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v_size_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; uint8_t v___y_4218_; lean_object* v___y_4219_; uint8_t v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v_size_4224_; uint8_t v_interpreted_4225_; uint8_t v_ctor_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; uint8_t v___y_4237_; lean_object* v___y_4238_; uint8_t v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; uint8_t v___y_4247_; lean_object* v___y_4258_; uint8_t v_interpreted_4259_; lean_object* v___y_4260_; uint8_t v_valueInconsistency_4261_; uint8_t v_trueEqFalse_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4275_; lean_object* v___y_4276_; uint8_t v_valueInconsistency_4277_; uint8_t v_trueEqFalse_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; uint8_t v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; uint8_t v___y_4345_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; 
v_options_4036_ = lean_ctor_get(v_a_4021_, 2);
v_inheritedTraceOptions_4037_ = lean_ctor_get(v_a_4021_, 13);
v_hasTrace_4038_ = lean_ctor_get_uint8(v_options_4036_, sizeof(void*)*1);
v___x_4039_ = 1;
if (v_hasTrace_4038_ == 0)
{
v___y_4352_ = v_a_4013_;
v___y_4353_ = v_a_4014_;
v___y_4354_ = v_a_4015_;
v___y_4355_ = v_a_4016_;
v___y_4356_ = v_a_4017_;
v___y_4357_ = v_a_4018_;
v___y_4358_ = v_a_4019_;
v___y_4359_ = v_a_4020_;
v___y_4360_ = v_a_4021_;
v___y_4361_ = v_a_4022_;
goto v___jp_4351_;
}
else
{
lean_object* v___x_4387_; lean_object* v___y_4389_; lean_object* v___x_4401_; uint8_t v___x_4402_; 
v___x_4387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4401_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4402_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4037_, v_options_4036_, v___x_4401_);
if (v___x_4402_ == 0)
{
v___y_4352_ = v_a_4013_;
v___y_4353_ = v_a_4014_;
v___y_4354_ = v_a_4015_;
v___y_4355_ = v_a_4016_;
v___y_4356_ = v_a_4017_;
v___y_4357_ = v_a_4018_;
v___y_4358_ = v_a_4019_;
v___y_4359_ = v_a_4020_;
v___y_4360_ = v_a_4021_;
v___y_4361_ = v_a_4022_;
goto v___jp_4351_;
}
else
{
lean_object* v___x_4403_; 
v___x_4403_ = l_Lean_Meta_Grind_updateLastTag(v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_dec_ref_known(v___x_4403_, 1);
if (v_isHEq_4012_ == 0)
{
lean_object* v___x_4404_; 
lean_inc_ref(v_rhs_4010_);
lean_inc_ref(v_lhs_4009_);
v___x_4404_ = l_Lean_Meta_mkEq(v_lhs_4009_, v_rhs_4010_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
v___y_4389_ = v___x_4404_;
goto v___jp_4388_;
}
else
{
lean_object* v___x_4405_; 
lean_inc_ref(v_rhs_4010_);
lean_inc_ref(v_lhs_4009_);
v___x_4405_ = l_Lean_Meta_mkHEq(v_lhs_4009_, v_rhs_4010_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
v___y_4389_ = v___x_4405_;
goto v___jp_4388_;
}
}
else
{
lean_dec(v_a_4032_);
lean_dec(v_a_4029_);
lean_dec_ref(v_proof_4011_);
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
return v___x_4403_;
}
}
v___jp_4388_:
{
if (lean_obj_tag(v___y_4389_) == 0)
{
lean_object* v_a_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v_a_4390_ = lean_ctor_get(v___y_4389_, 0);
lean_inc(v_a_4390_);
lean_dec_ref_known(v___y_4389_, 1);
v___x_4391_ = l_Lean_MessageData_ofExpr(v_a_4390_);
v___x_4392_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4387_, v___x_4391_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_dec_ref_known(v___x_4392_, 1);
v___y_4352_ = v_a_4013_;
v___y_4353_ = v_a_4014_;
v___y_4354_ = v_a_4015_;
v___y_4355_ = v_a_4016_;
v___y_4356_ = v_a_4017_;
v___y_4357_ = v_a_4018_;
v___y_4358_ = v_a_4019_;
v___y_4359_ = v_a_4020_;
v___y_4360_ = v_a_4021_;
v___y_4361_ = v_a_4022_;
goto v___jp_4351_;
}
else
{
lean_dec(v_a_4032_);
lean_dec(v_a_4029_);
lean_dec_ref(v_proof_4011_);
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
return v___x_4392_;
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_dec(v_a_4032_);
lean_dec(v_a_4029_);
lean_dec_ref(v_proof_4011_);
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
v_a_4393_ = lean_ctor_get(v___y_4389_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___y_4389_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___y_4389_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___y_4389_);
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
}
v___jp_4040_:
{
lean_object* v_options_4051_; uint8_t v_hasTrace_4052_; 
v_options_4051_ = lean_ctor_get(v___y_4049_, 2);
v_hasTrace_4052_ = lean_ctor_get_uint8(v_options_4051_, sizeof(void*)*1);
if (v_hasTrace_4052_ == 0)
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Lean_Meta_Grind_checkInvariants(v___x_4035_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
return v___x_4053_;
}
else
{
lean_object* v_inheritedTraceOptions_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v_inheritedTraceOptions_4054_ = lean_ctor_get(v___y_4049_, 13);
v___x_4055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4056_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4057_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4054_, v_options_4051_, v___x_4056_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Lean_Meta_Grind_checkInvariants(v___x_4035_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
return v___x_4058_;
}
else
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Lean_Meta_Grind_updateLastTag(v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
lean_dec_ref_known(v___x_4059_, 1);
v___x_4060_ = lean_st_ref_get(v___y_4041_);
v___x_4061_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4060_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___x_4060_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
v___x_4063_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
lean_ctor_set(v___x_4064_, 1, v_a_4062_);
v___x_4065_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4055_, v___x_4064_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v___x_4066_; 
lean_dec_ref_known(v___x_4065_, 1);
v___x_4066_ = l_Lean_Meta_Grind_checkInvariants(v___x_4035_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
return v___x_4066_;
}
else
{
return v___x_4065_;
}
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
v_a_4067_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4061_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4061_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
else
{
return v___x_4059_;
}
}
}
}
v___jp_4075_:
{
lean_object* v___x_4089_; 
v___x_4089_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4079_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; uint8_t v___x_4091_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4090_);
lean_dec_ref_known(v___x_4089_, 1);
v___x_4091_ = lean_unbox(v_a_4090_);
lean_dec(v_a_4090_);
if (v___x_4091_ == 0)
{
if (v___y_4078_ == 0)
{
lean_dec_ref(v___y_4077_);
lean_dec_ref(v___y_4076_);
v___y_4041_ = v___y_4079_;
v___y_4042_ = v___y_4080_;
v___y_4043_ = v___y_4081_;
v___y_4044_ = v___y_4082_;
v___y_4045_ = v___y_4083_;
v___y_4046_ = v___y_4084_;
v___y_4047_ = v___y_4085_;
v___y_4048_ = v___y_4086_;
v___y_4049_ = v___y_4087_;
v___y_4050_ = v___y_4088_;
goto v___jp_4040_;
}
else
{
lean_object* v_self_4092_; lean_object* v_self_4093_; lean_object* v___x_4094_; 
v_self_4092_ = lean_ctor_get(v___y_4076_, 0);
lean_inc_ref(v_self_4092_);
lean_dec_ref(v___y_4076_);
v_self_4093_ = lean_ctor_get(v___y_4077_, 0);
lean_inc_ref(v_self_4093_);
lean_dec_ref(v___y_4077_);
v___x_4094_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4092_, v_self_4093_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_dec_ref_known(v___x_4094_, 1);
v___y_4041_ = v___y_4079_;
v___y_4042_ = v___y_4080_;
v___y_4043_ = v___y_4081_;
v___y_4044_ = v___y_4082_;
v___y_4045_ = v___y_4083_;
v___y_4046_ = v___y_4084_;
v___y_4047_ = v___y_4085_;
v___y_4048_ = v___y_4086_;
v___y_4049_ = v___y_4087_;
v___y_4050_ = v___y_4088_;
goto v___jp_4040_;
}
else
{
return v___x_4094_;
}
}
}
else
{
lean_dec_ref(v___y_4077_);
lean_dec_ref(v___y_4076_);
v___y_4041_ = v___y_4079_;
v___y_4042_ = v___y_4080_;
v___y_4043_ = v___y_4081_;
v___y_4044_ = v___y_4082_;
v___y_4045_ = v___y_4083_;
v___y_4046_ = v___y_4084_;
v___y_4047_ = v___y_4085_;
v___y_4048_ = v___y_4086_;
v___y_4049_ = v___y_4087_;
v___y_4050_ = v___y_4088_;
goto v___jp_4040_;
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_dec_ref(v___y_4077_);
lean_dec_ref(v___y_4076_);
v_a_4095_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4089_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4089_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
v___jp_4103_:
{
if (v___y_4117_ == 0)
{
v___y_4076_ = v___y_4104_;
v___y_4077_ = v___y_4111_;
v___y_4078_ = v___y_4106_;
v___y_4079_ = v___y_4108_;
v___y_4080_ = v___y_4115_;
v___y_4081_ = v___y_4109_;
v___y_4082_ = v___y_4114_;
v___y_4083_ = v___y_4107_;
v___y_4084_ = v___y_4116_;
v___y_4085_ = v___y_4110_;
v___y_4086_ = v___y_4113_;
v___y_4087_ = v___y_4112_;
v___y_4088_ = v___y_4105_;
goto v___jp_4075_;
}
else
{
lean_object* v_self_4118_; lean_object* v_self_4119_; lean_object* v___x_4120_; 
v_self_4118_ = lean_ctor_get(v___y_4104_, 0);
v_self_4119_ = lean_ctor_get(v___y_4111_, 0);
lean_inc_ref(v_self_4119_);
lean_inc_ref(v_self_4118_);
v___x_4120_ = l_Lean_Meta_Grind_propagateCtor(v_self_4118_, v_self_4119_, v___y_4108_, v___y_4115_, v___y_4109_, v___y_4114_, v___y_4107_, v___y_4116_, v___y_4110_, v___y_4113_, v___y_4112_, v___y_4105_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_dec_ref_known(v___x_4120_, 1);
v___y_4076_ = v___y_4104_;
v___y_4077_ = v___y_4111_;
v___y_4078_ = v___y_4106_;
v___y_4079_ = v___y_4108_;
v___y_4080_ = v___y_4115_;
v___y_4081_ = v___y_4109_;
v___y_4082_ = v___y_4114_;
v___y_4083_ = v___y_4107_;
v___y_4084_ = v___y_4116_;
v___y_4085_ = v___y_4110_;
v___y_4086_ = v___y_4113_;
v___y_4087_ = v___y_4112_;
v___y_4088_ = v___y_4105_;
goto v___jp_4075_;
}
else
{
lean_dec_ref(v___y_4111_);
lean_dec_ref(v___y_4104_);
return v___x_4120_;
}
}
}
v___jp_4121_:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4125_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; uint8_t v___x_4137_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4135_, 1);
v___x_4137_ = lean_unbox(v_a_4136_);
lean_dec(v_a_4136_);
if (v___x_4137_ == 0)
{
uint8_t v_ctor_4138_; 
v_ctor_4138_ = lean_ctor_get_uint8(v___y_4122_, sizeof(void*)*12 + 2);
if (v_ctor_4138_ == 0)
{
v___y_4104_ = v___y_4122_;
v___y_4105_ = v___y_4134_;
v___y_4106_ = v___y_4124_;
v___y_4107_ = v___y_4129_;
v___y_4108_ = v___y_4125_;
v___y_4109_ = v___y_4127_;
v___y_4110_ = v___y_4131_;
v___y_4111_ = v___y_4123_;
v___y_4112_ = v___y_4133_;
v___y_4113_ = v___y_4132_;
v___y_4114_ = v___y_4128_;
v___y_4115_ = v___y_4126_;
v___y_4116_ = v___y_4130_;
v___y_4117_ = v___x_4035_;
goto v___jp_4103_;
}
else
{
uint8_t v_ctor_4139_; 
v_ctor_4139_ = lean_ctor_get_uint8(v___y_4123_, sizeof(void*)*12 + 2);
v___y_4104_ = v___y_4122_;
v___y_4105_ = v___y_4134_;
v___y_4106_ = v___y_4124_;
v___y_4107_ = v___y_4129_;
v___y_4108_ = v___y_4125_;
v___y_4109_ = v___y_4127_;
v___y_4110_ = v___y_4131_;
v___y_4111_ = v___y_4123_;
v___y_4112_ = v___y_4133_;
v___y_4113_ = v___y_4132_;
v___y_4114_ = v___y_4128_;
v___y_4115_ = v___y_4126_;
v___y_4116_ = v___y_4130_;
v___y_4117_ = v_ctor_4139_;
goto v___jp_4103_;
}
}
else
{
v___y_4076_ = v___y_4122_;
v___y_4077_ = v___y_4123_;
v___y_4078_ = v___y_4124_;
v___y_4079_ = v___y_4125_;
v___y_4080_ = v___y_4126_;
v___y_4081_ = v___y_4127_;
v___y_4082_ = v___y_4128_;
v___y_4083_ = v___y_4129_;
v___y_4084_ = v___y_4130_;
v___y_4085_ = v___y_4131_;
v___y_4086_ = v___y_4132_;
v___y_4087_ = v___y_4133_;
v___y_4088_ = v___y_4134_;
goto v___jp_4075_;
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v___y_4123_);
lean_dec_ref(v___y_4122_);
v_a_4140_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4135_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4135_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
v___jp_4148_:
{
if (v___y_4152_ == 0)
{
v___y_4122_ = v___y_4149_;
v___y_4123_ = v___y_4150_;
v___y_4124_ = v___y_4151_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
v___y_4129_ = v___y_4157_;
v___y_4130_ = v___y_4158_;
v___y_4131_ = v___y_4159_;
v___y_4132_ = v___y_4160_;
v___y_4133_ = v___y_4161_;
v___y_4134_ = v___y_4162_;
goto v___jp_4121_;
}
else
{
lean_object* v___x_4163_; 
v___x_4163_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_dec_ref_known(v___x_4163_, 1);
v___y_4122_ = v___y_4149_;
v___y_4123_ = v___y_4150_;
v___y_4124_ = v___y_4151_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
v___y_4129_ = v___y_4157_;
v___y_4130_ = v___y_4158_;
v___y_4131_ = v___y_4159_;
v___y_4132_ = v___y_4160_;
v___y_4133_ = v___y_4161_;
v___y_4134_ = v___y_4162_;
goto v___jp_4121_;
}
else
{
lean_dec_ref(v___y_4150_);
lean_dec_ref(v___y_4149_);
return v___x_4163_;
}
}
}
v___jp_4164_:
{
lean_object* v___x_4179_; 
lean_inc_ref(v___y_4166_);
lean_inc_ref(v___y_4174_);
v___x_4179_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4011_, v_isHEq_4012_, v_rhs_4010_, v_lhs_4009_, v_a_4032_, v_a_4029_, v___y_4174_, v___y_4166_, v___x_4039_, v___y_4170_, v___y_4178_, v___y_4167_, v___y_4172_, v___y_4165_, v___y_4175_, v___y_4176_, v___y_4168_, v___y_4177_, v___y_4173_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_dec_ref_known(v___x_4179_, 1);
v___y_4149_ = v___y_4166_;
v___y_4150_ = v___y_4174_;
v___y_4151_ = v___y_4169_;
v___y_4152_ = v___y_4171_;
v___y_4153_ = v___y_4170_;
v___y_4154_ = v___y_4178_;
v___y_4155_ = v___y_4167_;
v___y_4156_ = v___y_4172_;
v___y_4157_ = v___y_4165_;
v___y_4158_ = v___y_4175_;
v___y_4159_ = v___y_4176_;
v___y_4160_ = v___y_4168_;
v___y_4161_ = v___y_4177_;
v___y_4162_ = v___y_4173_;
goto v___jp_4148_;
}
else
{
lean_dec_ref(v___y_4174_);
lean_dec_ref(v___y_4166_);
return v___x_4179_;
}
}
v___jp_4180_:
{
lean_object* v___x_4195_; 
lean_inc_ref(v___y_4190_);
lean_inc_ref(v___y_4182_);
v___x_4195_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4011_, v_isHEq_4012_, v_lhs_4009_, v_rhs_4010_, v_a_4029_, v_a_4032_, v___y_4182_, v___y_4190_, v___x_4035_, v___y_4186_, v___y_4194_, v___y_4183_, v___y_4188_, v___y_4181_, v___y_4191_, v___y_4192_, v___y_4184_, v___y_4193_, v___y_4189_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_dec_ref_known(v___x_4195_, 1);
v___y_4149_ = v___y_4182_;
v___y_4150_ = v___y_4190_;
v___y_4151_ = v___y_4185_;
v___y_4152_ = v___y_4187_;
v___y_4153_ = v___y_4186_;
v___y_4154_ = v___y_4194_;
v___y_4155_ = v___y_4183_;
v___y_4156_ = v___y_4188_;
v___y_4157_ = v___y_4181_;
v___y_4158_ = v___y_4191_;
v___y_4159_ = v___y_4192_;
v___y_4160_ = v___y_4184_;
v___y_4161_ = v___y_4193_;
v___y_4162_ = v___y_4189_;
goto v___jp_4148_;
}
else
{
lean_dec_ref(v___y_4190_);
lean_dec_ref(v___y_4182_);
return v___x_4195_;
}
}
v___jp_4196_:
{
if (v___y_4211_ == 0)
{
v___y_4181_ = v___y_4197_;
v___y_4182_ = v___y_4198_;
v___y_4183_ = v___y_4199_;
v___y_4184_ = v___y_4200_;
v___y_4185_ = v___y_4201_;
v___y_4186_ = v___y_4202_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4204_;
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4206_;
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4209_;
v___y_4193_ = v___y_4208_;
v___y_4194_ = v___y_4210_;
goto v___jp_4180_;
}
else
{
v___y_4165_ = v___y_4197_;
v___y_4166_ = v___y_4198_;
v___y_4167_ = v___y_4199_;
v___y_4168_ = v___y_4200_;
v___y_4169_ = v___y_4201_;
v___y_4170_ = v___y_4202_;
v___y_4171_ = v___y_4203_;
v___y_4172_ = v___y_4204_;
v___y_4173_ = v___y_4205_;
v___y_4174_ = v___y_4206_;
v___y_4175_ = v___y_4207_;
v___y_4176_ = v___y_4209_;
v___y_4177_ = v___y_4208_;
v___y_4178_ = v___y_4210_;
goto v___jp_4164_;
}
}
v___jp_4212_:
{
uint8_t v___x_4231_; 
v___x_4231_ = lean_nat_dec_lt(v_size_4224_, v_size_4215_);
lean_dec(v_size_4215_);
lean_dec(v_size_4224_);
if (v___x_4231_ == 0)
{
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4216_;
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4219_;
v___y_4203_ = v___y_4220_;
v___y_4204_ = v___y_4221_;
v___y_4205_ = v___y_4222_;
v___y_4206_ = v___y_4223_;
v___y_4207_ = v___y_4227_;
v___y_4208_ = v___y_4229_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4230_;
v___y_4211_ = v___x_4035_;
goto v___jp_4196_;
}
else
{
if (v_interpreted_4225_ == 0)
{
if (v___x_4231_ == 0)
{
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4216_;
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4219_;
v___y_4203_ = v___y_4220_;
v___y_4204_ = v___y_4221_;
v___y_4205_ = v___y_4222_;
v___y_4206_ = v___y_4223_;
v___y_4207_ = v___y_4227_;
v___y_4208_ = v___y_4229_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4230_;
v___y_4211_ = v___x_4035_;
goto v___jp_4196_;
}
else
{
if (v_ctor_4226_ == 0)
{
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4216_;
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4219_;
v___y_4203_ = v___y_4220_;
v___y_4204_ = v___y_4221_;
v___y_4205_ = v___y_4222_;
v___y_4206_ = v___y_4223_;
v___y_4207_ = v___y_4227_;
v___y_4208_ = v___y_4229_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4230_;
v___y_4211_ = v___x_4231_;
goto v___jp_4196_;
}
else
{
v___y_4181_ = v___y_4213_;
v___y_4182_ = v___y_4214_;
v___y_4183_ = v___y_4216_;
v___y_4184_ = v___y_4217_;
v___y_4185_ = v___y_4218_;
v___y_4186_ = v___y_4219_;
v___y_4187_ = v___y_4220_;
v___y_4188_ = v___y_4221_;
v___y_4189_ = v___y_4222_;
v___y_4190_ = v___y_4223_;
v___y_4191_ = v___y_4227_;
v___y_4192_ = v___y_4228_;
v___y_4193_ = v___y_4229_;
v___y_4194_ = v___y_4230_;
goto v___jp_4180_;
}
}
}
else
{
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4216_;
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4219_;
v___y_4203_ = v___y_4220_;
v___y_4204_ = v___y_4221_;
v___y_4205_ = v___y_4222_;
v___y_4206_ = v___y_4223_;
v___y_4207_ = v___y_4227_;
v___y_4208_ = v___y_4229_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4230_;
v___y_4211_ = v___x_4035_;
goto v___jp_4196_;
}
}
}
v___jp_4232_:
{
if (v___y_4247_ == 0)
{
uint8_t v_ctor_4248_; 
v_ctor_4248_ = lean_ctor_get_uint8(v___y_4234_, sizeof(void*)*12 + 2);
if (v_ctor_4248_ == 0)
{
if (v___x_4035_ == 0)
{
lean_object* v_size_4249_; lean_object* v_size_4250_; uint8_t v_interpreted_4251_; uint8_t v_ctor_4252_; 
v_size_4249_ = lean_ctor_get(v___y_4234_, 6);
lean_inc(v_size_4249_);
v_size_4250_ = lean_ctor_get(v___y_4242_, 6);
lean_inc(v_size_4250_);
v_interpreted_4251_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 1);
v_ctor_4252_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 2);
v___y_4213_ = v___y_4233_;
v___y_4214_ = v___y_4234_;
v_size_4215_ = v_size_4249_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v___y_4218_ = v___y_4237_;
v___y_4219_ = v___y_4238_;
v___y_4220_ = v___y_4239_;
v___y_4221_ = v___y_4240_;
v___y_4222_ = v___y_4241_;
v___y_4223_ = v___y_4242_;
v_size_4224_ = v_size_4250_;
v_interpreted_4225_ = v_interpreted_4251_;
v_ctor_4226_ = v_ctor_4252_;
v___y_4227_ = v___y_4243_;
v___y_4228_ = v___y_4245_;
v___y_4229_ = v___y_4244_;
v___y_4230_ = v___y_4246_;
goto v___jp_4212_;
}
else
{
v___y_4165_ = v___y_4233_;
v___y_4166_ = v___y_4234_;
v___y_4167_ = v___y_4235_;
v___y_4168_ = v___y_4236_;
v___y_4169_ = v___y_4237_;
v___y_4170_ = v___y_4238_;
v___y_4171_ = v___y_4239_;
v___y_4172_ = v___y_4240_;
v___y_4173_ = v___y_4241_;
v___y_4174_ = v___y_4242_;
v___y_4175_ = v___y_4243_;
v___y_4176_ = v___y_4245_;
v___y_4177_ = v___y_4244_;
v___y_4178_ = v___y_4246_;
goto v___jp_4164_;
}
}
else
{
uint8_t v_ctor_4253_; 
v_ctor_4253_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 2);
if (v_ctor_4253_ == 0)
{
v___y_4165_ = v___y_4233_;
v___y_4166_ = v___y_4234_;
v___y_4167_ = v___y_4235_;
v___y_4168_ = v___y_4236_;
v___y_4169_ = v___y_4237_;
v___y_4170_ = v___y_4238_;
v___y_4171_ = v___y_4239_;
v___y_4172_ = v___y_4240_;
v___y_4173_ = v___y_4241_;
v___y_4174_ = v___y_4242_;
v___y_4175_ = v___y_4243_;
v___y_4176_ = v___y_4245_;
v___y_4177_ = v___y_4244_;
v___y_4178_ = v___y_4246_;
goto v___jp_4164_;
}
else
{
lean_object* v_size_4254_; lean_object* v_size_4255_; uint8_t v_interpreted_4256_; 
v_size_4254_ = lean_ctor_get(v___y_4234_, 6);
lean_inc(v_size_4254_);
v_size_4255_ = lean_ctor_get(v___y_4242_, 6);
lean_inc(v_size_4255_);
v_interpreted_4256_ = lean_ctor_get_uint8(v___y_4242_, sizeof(void*)*12 + 1);
v___y_4213_ = v___y_4233_;
v___y_4214_ = v___y_4234_;
v_size_4215_ = v_size_4254_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v___y_4218_ = v___y_4237_;
v___y_4219_ = v___y_4238_;
v___y_4220_ = v___y_4239_;
v___y_4221_ = v___y_4240_;
v___y_4222_ = v___y_4241_;
v___y_4223_ = v___y_4242_;
v_size_4224_ = v_size_4255_;
v_interpreted_4225_ = v_interpreted_4256_;
v_ctor_4226_ = v_ctor_4253_;
v___y_4227_ = v___y_4243_;
v___y_4228_ = v___y_4245_;
v___y_4229_ = v___y_4244_;
v___y_4230_ = v___y_4246_;
goto v___jp_4212_;
}
}
}
else
{
v___y_4165_ = v___y_4233_;
v___y_4166_ = v___y_4234_;
v___y_4167_ = v___y_4235_;
v___y_4168_ = v___y_4236_;
v___y_4169_ = v___y_4237_;
v___y_4170_ = v___y_4238_;
v___y_4171_ = v___y_4239_;
v___y_4172_ = v___y_4240_;
v___y_4173_ = v___y_4241_;
v___y_4174_ = v___y_4242_;
v___y_4175_ = v___y_4243_;
v___y_4176_ = v___y_4245_;
v___y_4177_ = v___y_4244_;
v___y_4178_ = v___y_4246_;
goto v___jp_4164_;
}
}
v___jp_4257_:
{
if (v_interpreted_4259_ == 0)
{
v___y_4233_ = v___y_4267_;
v___y_4234_ = v___y_4258_;
v___y_4235_ = v___y_4265_;
v___y_4236_ = v___y_4270_;
v___y_4237_ = v_valueInconsistency_4261_;
v___y_4238_ = v___y_4263_;
v___y_4239_ = v_trueEqFalse_4262_;
v___y_4240_ = v___y_4266_;
v___y_4241_ = v___y_4272_;
v___y_4242_ = v___y_4260_;
v___y_4243_ = v___y_4268_;
v___y_4244_ = v___y_4271_;
v___y_4245_ = v___y_4269_;
v___y_4246_ = v___y_4264_;
v___y_4247_ = v___x_4035_;
goto v___jp_4232_;
}
else
{
uint8_t v_interpreted_4273_; 
v_interpreted_4273_ = lean_ctor_get_uint8(v___y_4260_, sizeof(void*)*12 + 1);
if (v_interpreted_4273_ == 0)
{
v___y_4165_ = v___y_4267_;
v___y_4166_ = v___y_4258_;
v___y_4167_ = v___y_4265_;
v___y_4168_ = v___y_4270_;
v___y_4169_ = v_valueInconsistency_4261_;
v___y_4170_ = v___y_4263_;
v___y_4171_ = v_trueEqFalse_4262_;
v___y_4172_ = v___y_4266_;
v___y_4173_ = v___y_4272_;
v___y_4174_ = v___y_4260_;
v___y_4175_ = v___y_4268_;
v___y_4176_ = v___y_4269_;
v___y_4177_ = v___y_4271_;
v___y_4178_ = v___y_4264_;
goto v___jp_4164_;
}
else
{
v___y_4233_ = v___y_4267_;
v___y_4234_ = v___y_4258_;
v___y_4235_ = v___y_4265_;
v___y_4236_ = v___y_4270_;
v___y_4237_ = v_valueInconsistency_4261_;
v___y_4238_ = v___y_4263_;
v___y_4239_ = v_trueEqFalse_4262_;
v___y_4240_ = v___y_4266_;
v___y_4241_ = v___y_4272_;
v___y_4242_ = v___y_4260_;
v___y_4243_ = v___y_4268_;
v___y_4244_ = v___y_4271_;
v___y_4245_ = v___y_4269_;
v___y_4246_ = v___y_4264_;
v___y_4247_ = v___x_4035_;
goto v___jp_4232_;
}
}
}
v___jp_4274_:
{
uint8_t v_interpreted_4289_; 
v_interpreted_4289_ = lean_ctor_get_uint8(v___y_4275_, sizeof(void*)*12 + 1);
v___y_4258_ = v___y_4275_;
v_interpreted_4259_ = v_interpreted_4289_;
v___y_4260_ = v___y_4276_;
v_valueInconsistency_4261_ = v_valueInconsistency_4277_;
v_trueEqFalse_4262_ = v_trueEqFalse_4278_;
v___y_4263_ = v___y_4279_;
v___y_4264_ = v___y_4280_;
v___y_4265_ = v___y_4281_;
v___y_4266_ = v___y_4282_;
v___y_4267_ = v___y_4283_;
v___y_4268_ = v___y_4284_;
v___y_4269_ = v___y_4285_;
v___y_4270_ = v___y_4286_;
v___y_4271_ = v___y_4287_;
v___y_4272_ = v___y_4288_;
goto v___jp_4257_;
}
v___jp_4290_:
{
lean_object* v___x_4303_; 
v___x_4303_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4291_, v___y_4297_, v___y_4301_, v___y_4299_, v___y_4298_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_dec_ref_known(v___x_4303_, 1);
v___y_4275_ = v___y_4292_;
v___y_4276_ = v___y_4300_;
v_valueInconsistency_4277_ = v___x_4035_;
v_trueEqFalse_4278_ = v___x_4039_;
v___y_4279_ = v___y_4291_;
v___y_4280_ = v___y_4293_;
v___y_4281_ = v___y_4302_;
v___y_4282_ = v___y_4294_;
v___y_4283_ = v___y_4295_;
v___y_4284_ = v___y_4296_;
v___y_4285_ = v___y_4297_;
v___y_4286_ = v___y_4301_;
v___y_4287_ = v___y_4299_;
v___y_4288_ = v___y_4298_;
goto v___jp_4274_;
}
else
{
lean_dec_ref(v___y_4300_);
lean_dec_ref(v___y_4292_);
lean_dec(v_a_4032_);
lean_dec(v_a_4029_);
lean_dec_ref(v_proof_4011_);
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
return v___x_4303_;
}
}
v___jp_4304_:
{
if (v___y_4312_ == 0)
{
lean_object* v_self_4318_; uint8_t v_interpreted_4319_; lean_object* v_self_4320_; lean_object* v___x_4321_; 
v_self_4318_ = lean_ctor_get(v___y_4306_, 0);
v_interpreted_4319_ = lean_ctor_get_uint8(v___y_4306_, sizeof(void*)*12 + 1);
v_self_4320_ = lean_ctor_get(v___y_4315_, 0);
lean_inc_ref(v_self_4320_);
lean_inc_ref(v_self_4318_);
v___x_4321_ = l_Lean_Meta_Grind_hasSameType(v_self_4318_, v_self_4320_, v___y_4311_, v___y_4316_, v___y_4314_, v___y_4313_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; uint8_t v___x_4323_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4321_, 1);
v___x_4323_ = lean_unbox(v_a_4322_);
lean_dec(v_a_4322_);
if (v___x_4323_ == 0)
{
v___y_4258_ = v___y_4306_;
v_interpreted_4259_ = v_interpreted_4319_;
v___y_4260_ = v___y_4315_;
v_valueInconsistency_4261_ = v___x_4035_;
v_trueEqFalse_4262_ = v___x_4035_;
v___y_4263_ = v___y_4305_;
v___y_4264_ = v___y_4307_;
v___y_4265_ = v___y_4317_;
v___y_4266_ = v___y_4308_;
v___y_4267_ = v___y_4309_;
v___y_4268_ = v___y_4310_;
v___y_4269_ = v___y_4311_;
v___y_4270_ = v___y_4316_;
v___y_4271_ = v___y_4314_;
v___y_4272_ = v___y_4313_;
goto v___jp_4257_;
}
else
{
v___y_4258_ = v___y_4306_;
v_interpreted_4259_ = v_interpreted_4319_;
v___y_4260_ = v___y_4315_;
v_valueInconsistency_4261_ = v___x_4039_;
v_trueEqFalse_4262_ = v___x_4035_;
v___y_4263_ = v___y_4305_;
v___y_4264_ = v___y_4307_;
v___y_4265_ = v___y_4317_;
v___y_4266_ = v___y_4308_;
v___y_4267_ = v___y_4309_;
v___y_4268_ = v___y_4310_;
v___y_4269_ = v___y_4311_;
v___y_4270_ = v___y_4316_;
v___y_4271_ = v___y_4314_;
v___y_4272_ = v___y_4313_;
goto v___jp_4257_;
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
lean_dec_ref(v___y_4315_);
lean_dec_ref(v___y_4306_);
lean_dec(v_a_4032_);
lean_dec(v_a_4029_);
lean_dec_ref(v_proof_4011_);
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
v_a_4324_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4321_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4321_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
else
{
v___y_4275_ = v___y_4306_;
v___y_4276_ = v___y_4315_;
v_valueInconsistency_4277_ = v___x_4039_;
v_trueEqFalse_4278_ = v___x_4035_;
v___y_4279_ = v___y_4305_;
v___y_4280_ = v___y_4307_;
v___y_4281_ = v___y_4317_;
v___y_4282_ = v___y_4308_;
v___y_4283_ = v___y_4309_;
v___y_4284_ = v___y_4310_;
v___y_4285_ = v___y_4311_;
v___y_4286_ = v___y_4316_;
v___y_4287_ = v___y_4314_;
v___y_4288_ = v___y_4313_;
goto v___jp_4274_;
}
}
v___jp_4332_:
{
if (v___y_4345_ == 0)
{
v___y_4275_ = v___y_4334_;
v___y_4276_ = v___y_4342_;
v_valueInconsistency_4277_ = v___x_4035_;
v_trueEqFalse_4278_ = v___x_4035_;
v___y_4279_ = v___y_4333_;
v___y_4280_ = v___y_4335_;
v___y_4281_ = v___y_4344_;
v___y_4282_ = v___y_4336_;
v___y_4283_ = v___y_4337_;
v___y_4284_ = v___y_4338_;
v___y_4285_ = v___y_4339_;
v___y_4286_ = v___y_4343_;
v___y_4287_ = v___y_4341_;
v___y_4288_ = v___y_4340_;
goto v___jp_4274_;
}
else
{
uint8_t v___x_4346_; 
lean_inc_ref(v_root_4033_);
v___x_4346_ = l_Lean_Expr_isTrue(v_root_4033_);
if (v___x_4346_ == 0)
{
uint8_t v___x_4347_; 
lean_inc_ref(v_root_4034_);
v___x_4347_ = l_Lean_Expr_isTrue(v_root_4034_);
if (v___x_4347_ == 0)
{
if (v_isHEq_4012_ == 0)
{
uint8_t v_heqProofs_4348_; 
v_heqProofs_4348_ = lean_ctor_get_uint8(v___y_4334_, sizeof(void*)*12 + 4);
if (v_heqProofs_4348_ == 0)
{
uint8_t v_heqProofs_4349_; 
v_heqProofs_4349_ = lean_ctor_get_uint8(v___y_4342_, sizeof(void*)*12 + 4);
if (v_heqProofs_4349_ == 0)
{
uint8_t v_interpreted_4350_; 
v_interpreted_4350_ = lean_ctor_get_uint8(v___y_4334_, sizeof(void*)*12 + 1);
v___y_4258_ = v___y_4334_;
v_interpreted_4259_ = v_interpreted_4350_;
v___y_4260_ = v___y_4342_;
v_valueInconsistency_4261_ = v___x_4039_;
v_trueEqFalse_4262_ = v___x_4035_;
v___y_4263_ = v___y_4333_;
v___y_4264_ = v___y_4335_;
v___y_4265_ = v___y_4344_;
v___y_4266_ = v___y_4336_;
v___y_4267_ = v___y_4337_;
v___y_4268_ = v___y_4338_;
v___y_4269_ = v___y_4339_;
v___y_4270_ = v___y_4343_;
v___y_4271_ = v___y_4341_;
v___y_4272_ = v___y_4340_;
goto v___jp_4257_;
}
else
{
v___y_4305_ = v___y_4333_;
v___y_4306_ = v___y_4334_;
v___y_4307_ = v___y_4335_;
v___y_4308_ = v___y_4336_;
v___y_4309_ = v___y_4337_;
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4339_;
v___y_4312_ = v___x_4347_;
v___y_4313_ = v___y_4340_;
v___y_4314_ = v___y_4341_;
v___y_4315_ = v___y_4342_;
v___y_4316_ = v___y_4343_;
v___y_4317_ = v___y_4344_;
goto v___jp_4304_;
}
}
else
{
v___y_4305_ = v___y_4333_;
v___y_4306_ = v___y_4334_;
v___y_4307_ = v___y_4335_;
v___y_4308_ = v___y_4336_;
v___y_4309_ = v___y_4337_;
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4339_;
v___y_4312_ = v___x_4347_;
v___y_4313_ = v___y_4340_;
v___y_4314_ = v___y_4341_;
v___y_4315_ = v___y_4342_;
v___y_4316_ = v___y_4343_;
v___y_4317_ = v___y_4344_;
goto v___jp_4304_;
}
}
else
{
v___y_4305_ = v___y_4333_;
v___y_4306_ = v___y_4334_;
v___y_4307_ = v___y_4335_;
v___y_4308_ = v___y_4336_;
v___y_4309_ = v___y_4337_;
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4339_;
v___y_4312_ = v___x_4347_;
v___y_4313_ = v___y_4340_;
v___y_4314_ = v___y_4341_;
v___y_4315_ = v___y_4342_;
v___y_4316_ = v___y_4343_;
v___y_4317_ = v___y_4344_;
goto v___jp_4304_;
}
}
else
{
v___y_4291_ = v___y_4333_;
v___y_4292_ = v___y_4334_;
v___y_4293_ = v___y_4335_;
v___y_4294_ = v___y_4336_;
v___y_4295_ = v___y_4337_;
v___y_4296_ = v___y_4338_;
v___y_4297_ = v___y_4339_;
v___y_4298_ = v___y_4340_;
v___y_4299_ = v___y_4341_;
v___y_4300_ = v___y_4342_;
v___y_4301_ = v___y_4343_;
v___y_4302_ = v___y_4344_;
goto v___jp_4290_;
}
}
else
{
v___y_4291_ = v___y_4333_;
v___y_4292_ = v___y_4334_;
v___y_4293_ = v___y_4335_;
v___y_4294_ = v___y_4336_;
v___y_4295_ = v___y_4337_;
v___y_4296_ = v___y_4338_;
v___y_4297_ = v___y_4339_;
v___y_4298_ = v___y_4340_;
v___y_4299_ = v___y_4341_;
v___y_4300_ = v___y_4342_;
v___y_4301_ = v___y_4343_;
v___y_4302_ = v___y_4344_;
goto v___jp_4290_;
}
}
}
v___jp_4351_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4362_ = lean_st_ref_get(v___y_4352_);
lean_inc_ref(v_root_4033_);
v___x_4363_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4362_, v_root_4033_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___x_4362_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4363_, 1);
v___x_4365_ = lean_st_ref_get(v___y_4352_);
lean_inc_ref(v_root_4034_);
v___x_4366_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4365_, v_root_4034_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___x_4365_);
if (lean_obj_tag(v___x_4366_) == 0)
{
uint8_t v_interpreted_4367_; 
v_interpreted_4367_ = lean_ctor_get_uint8(v_a_4364_, sizeof(void*)*12 + 1);
if (v_interpreted_4367_ == 0)
{
lean_object* v_a_4368_; 
v_a_4368_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_a_4368_);
lean_dec_ref_known(v___x_4366_, 1);
v___y_4333_ = v___y_4352_;
v___y_4334_ = v_a_4364_;
v___y_4335_ = v___y_4353_;
v___y_4336_ = v___y_4355_;
v___y_4337_ = v___y_4356_;
v___y_4338_ = v___y_4357_;
v___y_4339_ = v___y_4358_;
v___y_4340_ = v___y_4361_;
v___y_4341_ = v___y_4360_;
v___y_4342_ = v_a_4368_;
v___y_4343_ = v___y_4359_;
v___y_4344_ = v___y_4354_;
v___y_4345_ = v___x_4035_;
goto v___jp_4332_;
}
else
{
lean_object* v_a_4369_; uint8_t v_interpreted_4370_; 
v_a_4369_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_a_4369_);
lean_dec_ref_known(v___x_4366_, 1);
v_interpreted_4370_ = lean_ctor_get_uint8(v_a_4369_, sizeof(void*)*12 + 1);
v___y_4333_ = v___y_4352_;
v___y_4334_ = v_a_4364_;
v___y_4335_ = v___y_4353_;
v___y_4336_ = v___y_4355_;
v___y_4337_ = v___y_4356_;
v___y_4338_ = v___y_4357_;
v___y_4339_ = v___y_4358_;
v___y_4340_ = v___y_4361_;
v___y_4341_ = v___y_4360_;
v___y_4342_ = v_a_4369_;
v___y_4343_ = v___y_4359_;
v___y_4344_ = v___y_4354_;
v___y_4345_ = v_interpreted_4370_;
goto v___jp_4332_;
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec(v_a_4364_);
lean_dec(v_a_4032_);
lean_dec(v_a_4029_);
lean_dec_ref(v_proof_4011_);
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
v_a_4371_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4366_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4366_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec(v_a_4032_);
lean_dec(v_a_4029_);
lean_dec_ref(v_proof_4011_);
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
v_a_4379_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4363_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4363_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
}
else
{
lean_object* v_options_4406_; uint8_t v_hasTrace_4407_; 
lean_dec(v_a_4032_);
lean_dec(v_a_4029_);
lean_dec_ref(v_proof_4011_);
v_options_4406_ = lean_ctor_get(v_a_4021_, 2);
v_hasTrace_4407_ = lean_ctor_get_uint8(v_options_4406_, sizeof(void*)*1);
if (v_hasTrace_4407_ == 0)
{
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
goto v___jp_4024_;
}
else
{
lean_object* v_inheritedTraceOptions_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; uint8_t v___x_4411_; 
v_inheritedTraceOptions_4408_ = lean_ctor_get(v_a_4021_, 13);
v___x_4409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4411_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4408_, v_options_4406_, v___x_4410_);
if (v___x_4411_ == 0)
{
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
goto v___jp_4024_;
}
else
{
lean_object* v___x_4412_; 
v___x_4412_ = l_Lean_Meta_Grind_updateLastTag(v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v___x_4413_; 
lean_dec_ref_known(v___x_4412_, 1);
v___x_4413_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4009_, v_a_4013_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4415_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v___x_4415_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4010_, v_a_4013_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4416_);
lean_dec_ref_known(v___x_4415_, 1);
v___x_4417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4418_, 0, v_a_4414_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v___x_4419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
lean_ctor_set(v___x_4419_, 1, v_a_4416_);
v___x_4420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4419_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4409_, v___x_4421_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_dec_ref_known(v___x_4422_, 1);
goto v___jp_4024_;
}
else
{
return v___x_4422_;
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v_a_4414_);
v_a_4423_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4415_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4415_);
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
}
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_dec_ref(v_rhs_4010_);
v_a_4431_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4413_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4413_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
return v___x_4412_;
}
}
}
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_dec(v_a_4029_);
lean_dec_ref(v_proof_4011_);
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
v_a_4439_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4031_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4031_);
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
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec_ref(v_proof_4011_);
lean_dec_ref(v_rhs_4010_);
lean_dec_ref(v_lhs_4009_);
v_a_4447_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4028_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4028_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
v___jp_4024_:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = lean_box(0);
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
return v___x_4026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4455_, lean_object* v_rhs_4456_, lean_object* v_proof_4457_, lean_object* v_isHEq_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
uint8_t v_isHEq_boxed_4470_; lean_object* v_res_4471_; 
v_isHEq_boxed_4470_ = lean_unbox(v_isHEq_4458_);
v_res_4471_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4455_, v_rhs_4456_, v_proof_4457_, v_isHEq_boxed_4470_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
lean_dec(v_a_4462_);
lean_dec_ref(v_a_4461_);
lean_dec(v_a_4460_);
lean_dec(v_a_4459_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4474_){
_start:
{
lean_object* v___x_4476_; lean_object* v_toGoalState_4477_; lean_object* v_mvarId_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4514_; 
v___x_4476_ = lean_st_ref_take(v_a_4474_);
v_toGoalState_4477_ = lean_ctor_get(v___x_4476_, 0);
v_mvarId_4478_ = lean_ctor_get(v___x_4476_, 1);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4480_ = v___x_4476_;
v_isShared_4481_ = v_isSharedCheck_4514_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_mvarId_4478_);
lean_inc(v_toGoalState_4477_);
lean_dec(v___x_4476_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4514_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v_nextDeclIdx_4482_; lean_object* v_enodeMap_4483_; lean_object* v_exprs_4484_; lean_object* v_parents_4485_; lean_object* v_congrTable_4486_; lean_object* v_appMap_4487_; lean_object* v_indicesFound_4488_; uint8_t v_inconsistent_4489_; lean_object* v_nextIdx_4490_; lean_object* v_newRawFacts_4491_; lean_object* v_facts_4492_; lean_object* v_extThms_4493_; lean_object* v_ematch_4494_; lean_object* v_inj_4495_; lean_object* v_split_4496_; lean_object* v_clean_4497_; lean_object* v_sstates_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4512_; 
v_nextDeclIdx_4482_ = lean_ctor_get(v_toGoalState_4477_, 0);
v_enodeMap_4483_ = lean_ctor_get(v_toGoalState_4477_, 1);
v_exprs_4484_ = lean_ctor_get(v_toGoalState_4477_, 2);
v_parents_4485_ = lean_ctor_get(v_toGoalState_4477_, 3);
v_congrTable_4486_ = lean_ctor_get(v_toGoalState_4477_, 4);
v_appMap_4487_ = lean_ctor_get(v_toGoalState_4477_, 5);
v_indicesFound_4488_ = lean_ctor_get(v_toGoalState_4477_, 6);
v_inconsistent_4489_ = lean_ctor_get_uint8(v_toGoalState_4477_, sizeof(void*)*17);
v_nextIdx_4490_ = lean_ctor_get(v_toGoalState_4477_, 8);
v_newRawFacts_4491_ = lean_ctor_get(v_toGoalState_4477_, 9);
v_facts_4492_ = lean_ctor_get(v_toGoalState_4477_, 10);
v_extThms_4493_ = lean_ctor_get(v_toGoalState_4477_, 11);
v_ematch_4494_ = lean_ctor_get(v_toGoalState_4477_, 12);
v_inj_4495_ = lean_ctor_get(v_toGoalState_4477_, 13);
v_split_4496_ = lean_ctor_get(v_toGoalState_4477_, 14);
v_clean_4497_ = lean_ctor_get(v_toGoalState_4477_, 15);
v_sstates_4498_ = lean_ctor_get(v_toGoalState_4477_, 16);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_toGoalState_4477_);
if (v_isSharedCheck_4512_ == 0)
{
lean_object* v_unused_4513_; 
v_unused_4513_ = lean_ctor_get(v_toGoalState_4477_, 7);
lean_dec(v_unused_4513_);
v___x_4500_ = v_toGoalState_4477_;
v_isShared_4501_ = v_isSharedCheck_4512_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_sstates_4498_);
lean_inc(v_clean_4497_);
lean_inc(v_split_4496_);
lean_inc(v_inj_4495_);
lean_inc(v_ematch_4494_);
lean_inc(v_extThms_4493_);
lean_inc(v_facts_4492_);
lean_inc(v_newRawFacts_4491_);
lean_inc(v_nextIdx_4490_);
lean_inc(v_indicesFound_4488_);
lean_inc(v_appMap_4487_);
lean_inc(v_congrTable_4486_);
lean_inc(v_parents_4485_);
lean_inc(v_exprs_4484_);
lean_inc(v_enodeMap_4483_);
lean_inc(v_nextDeclIdx_4482_);
lean_dec(v_toGoalState_4477_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4512_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4502_; lean_object* v___x_4504_; 
v___x_4502_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 7, v___x_4502_);
v___x_4504_ = v___x_4500_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_nextDeclIdx_4482_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_enodeMap_4483_);
lean_ctor_set(v_reuseFailAlloc_4511_, 2, v_exprs_4484_);
lean_ctor_set(v_reuseFailAlloc_4511_, 3, v_parents_4485_);
lean_ctor_set(v_reuseFailAlloc_4511_, 4, v_congrTable_4486_);
lean_ctor_set(v_reuseFailAlloc_4511_, 5, v_appMap_4487_);
lean_ctor_set(v_reuseFailAlloc_4511_, 6, v_indicesFound_4488_);
lean_ctor_set(v_reuseFailAlloc_4511_, 7, v___x_4502_);
lean_ctor_set(v_reuseFailAlloc_4511_, 8, v_nextIdx_4490_);
lean_ctor_set(v_reuseFailAlloc_4511_, 9, v_newRawFacts_4491_);
lean_ctor_set(v_reuseFailAlloc_4511_, 10, v_facts_4492_);
lean_ctor_set(v_reuseFailAlloc_4511_, 11, v_extThms_4493_);
lean_ctor_set(v_reuseFailAlloc_4511_, 12, v_ematch_4494_);
lean_ctor_set(v_reuseFailAlloc_4511_, 13, v_inj_4495_);
lean_ctor_set(v_reuseFailAlloc_4511_, 14, v_split_4496_);
lean_ctor_set(v_reuseFailAlloc_4511_, 15, v_clean_4497_);
lean_ctor_set(v_reuseFailAlloc_4511_, 16, v_sstates_4498_);
lean_ctor_set_uint8(v_reuseFailAlloc_4511_, sizeof(void*)*17, v_inconsistent_4489_);
v___x_4504_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
lean_object* v___x_4506_; 
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 0, v___x_4504_);
v___x_4506_ = v___x_4480_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4504_);
lean_ctor_set(v_reuseFailAlloc_4510_, 1, v_mvarId_4478_);
v___x_4506_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4507_ = lean_st_ref_set(v_a_4474_, v___x_4506_);
v___x_4508_ = lean_box(0);
v___x_4509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4508_);
return v___x_4509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4515_);
lean_dec(v_a_4515_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v___x_4529_; 
v___x_4529_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4518_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
lean_dec(v_a_4537_);
lean_dec_ref(v_a_4536_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
lean_dec(v_a_4531_);
lean_dec(v_a_4530_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4542_){
_start:
{
lean_object* v___x_4544_; lean_object* v_toGoalState_4545_; lean_object* v_newFacts_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; uint8_t v___x_4550_; 
v___x_4544_ = lean_st_ref_get(v_a_4542_);
v_toGoalState_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc_ref(v_toGoalState_4545_);
lean_dec(v___x_4544_);
v_newFacts_4546_ = lean_ctor_get(v_toGoalState_4545_, 7);
lean_inc_ref(v_newFacts_4546_);
lean_dec_ref(v_toGoalState_4545_);
v___x_4547_ = lean_array_get_size(v_newFacts_4546_);
v___x_4548_ = lean_unsigned_to_nat(1u);
v___x_4549_ = lean_nat_sub(v___x_4547_, v___x_4548_);
v___x_4550_ = lean_nat_dec_lt(v___x_4549_, v___x_4547_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
lean_dec(v___x_4549_);
lean_dec_ref(v_newFacts_4546_);
v___x_4551_ = lean_box(0);
v___x_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
return v___x_4552_;
}
else
{
lean_object* v___x_4553_; lean_object* v_toGoalState_4554_; lean_object* v_mvarId_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4592_; 
v___x_4553_ = lean_st_ref_take(v_a_4542_);
v_toGoalState_4554_ = lean_ctor_get(v___x_4553_, 0);
v_mvarId_4555_ = lean_ctor_get(v___x_4553_, 1);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4557_ = v___x_4553_;
v_isShared_4558_ = v_isSharedCheck_4592_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_mvarId_4555_);
lean_inc(v_toGoalState_4554_);
lean_dec(v___x_4553_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4592_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v_nextDeclIdx_4559_; lean_object* v_enodeMap_4560_; lean_object* v_exprs_4561_; lean_object* v_parents_4562_; lean_object* v_congrTable_4563_; lean_object* v_appMap_4564_; lean_object* v_indicesFound_4565_; lean_object* v_newFacts_4566_; uint8_t v_inconsistent_4567_; lean_object* v_nextIdx_4568_; lean_object* v_newRawFacts_4569_; lean_object* v_facts_4570_; lean_object* v_extThms_4571_; lean_object* v_ematch_4572_; lean_object* v_inj_4573_; lean_object* v_split_4574_; lean_object* v_clean_4575_; lean_object* v_sstates_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4591_; 
v_nextDeclIdx_4559_ = lean_ctor_get(v_toGoalState_4554_, 0);
v_enodeMap_4560_ = lean_ctor_get(v_toGoalState_4554_, 1);
v_exprs_4561_ = lean_ctor_get(v_toGoalState_4554_, 2);
v_parents_4562_ = lean_ctor_get(v_toGoalState_4554_, 3);
v_congrTable_4563_ = lean_ctor_get(v_toGoalState_4554_, 4);
v_appMap_4564_ = lean_ctor_get(v_toGoalState_4554_, 5);
v_indicesFound_4565_ = lean_ctor_get(v_toGoalState_4554_, 6);
v_newFacts_4566_ = lean_ctor_get(v_toGoalState_4554_, 7);
v_inconsistent_4567_ = lean_ctor_get_uint8(v_toGoalState_4554_, sizeof(void*)*17);
v_nextIdx_4568_ = lean_ctor_get(v_toGoalState_4554_, 8);
v_newRawFacts_4569_ = lean_ctor_get(v_toGoalState_4554_, 9);
v_facts_4570_ = lean_ctor_get(v_toGoalState_4554_, 10);
v_extThms_4571_ = lean_ctor_get(v_toGoalState_4554_, 11);
v_ematch_4572_ = lean_ctor_get(v_toGoalState_4554_, 12);
v_inj_4573_ = lean_ctor_get(v_toGoalState_4554_, 13);
v_split_4574_ = lean_ctor_get(v_toGoalState_4554_, 14);
v_clean_4575_ = lean_ctor_get(v_toGoalState_4554_, 15);
v_sstates_4576_ = lean_ctor_get(v_toGoalState_4554_, 16);
v_isSharedCheck_4591_ = !lean_is_exclusive(v_toGoalState_4554_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4578_ = v_toGoalState_4554_;
v_isShared_4579_ = v_isSharedCheck_4591_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_sstates_4576_);
lean_inc(v_clean_4575_);
lean_inc(v_split_4574_);
lean_inc(v_inj_4573_);
lean_inc(v_ematch_4572_);
lean_inc(v_extThms_4571_);
lean_inc(v_facts_4570_);
lean_inc(v_newRawFacts_4569_);
lean_inc(v_nextIdx_4568_);
lean_inc(v_newFacts_4566_);
lean_inc(v_indicesFound_4565_);
lean_inc(v_appMap_4564_);
lean_inc(v_congrTable_4563_);
lean_inc(v_parents_4562_);
lean_inc(v_exprs_4561_);
lean_inc(v_enodeMap_4560_);
lean_inc(v_nextDeclIdx_4559_);
lean_dec(v_toGoalState_4554_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4591_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4580_; lean_object* v___x_4582_; 
v___x_4580_ = lean_array_pop(v_newFacts_4566_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 7, v___x_4580_);
v___x_4582_ = v___x_4578_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_nextDeclIdx_4559_);
lean_ctor_set(v_reuseFailAlloc_4590_, 1, v_enodeMap_4560_);
lean_ctor_set(v_reuseFailAlloc_4590_, 2, v_exprs_4561_);
lean_ctor_set(v_reuseFailAlloc_4590_, 3, v_parents_4562_);
lean_ctor_set(v_reuseFailAlloc_4590_, 4, v_congrTable_4563_);
lean_ctor_set(v_reuseFailAlloc_4590_, 5, v_appMap_4564_);
lean_ctor_set(v_reuseFailAlloc_4590_, 6, v_indicesFound_4565_);
lean_ctor_set(v_reuseFailAlloc_4590_, 7, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4590_, 8, v_nextIdx_4568_);
lean_ctor_set(v_reuseFailAlloc_4590_, 9, v_newRawFacts_4569_);
lean_ctor_set(v_reuseFailAlloc_4590_, 10, v_facts_4570_);
lean_ctor_set(v_reuseFailAlloc_4590_, 11, v_extThms_4571_);
lean_ctor_set(v_reuseFailAlloc_4590_, 12, v_ematch_4572_);
lean_ctor_set(v_reuseFailAlloc_4590_, 13, v_inj_4573_);
lean_ctor_set(v_reuseFailAlloc_4590_, 14, v_split_4574_);
lean_ctor_set(v_reuseFailAlloc_4590_, 15, v_clean_4575_);
lean_ctor_set(v_reuseFailAlloc_4590_, 16, v_sstates_4576_);
lean_ctor_set_uint8(v_reuseFailAlloc_4590_, sizeof(void*)*17, v_inconsistent_4567_);
v___x_4582_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4584_; 
if (v_isShared_4558_ == 0)
{
lean_ctor_set(v___x_4557_, 0, v___x_4582_);
v___x_4584_ = v___x_4557_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4582_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_mvarId_4555_);
v___x_4584_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; 
v___x_4585_ = lean_st_ref_set(v_a_4542_, v___x_4584_);
v___x_4586_ = lean_array_fget(v_newFacts_4546_, v___x_4549_);
lean_dec(v___x_4549_);
lean_dec_ref(v_newFacts_4546_);
v___x_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
return v___x_4588_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4593_);
lean_dec(v_a_4593_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_){
_start:
{
lean_object* v___x_4607_; 
v___x_4607_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4596_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_);
lean_dec(v_a_4617_);
lean_dec_ref(v_a_4616_);
lean_dec(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec(v_a_4613_);
lean_dec_ref(v_a_4612_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
lean_dec(v_a_4608_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4620_, lean_object* v_rhs_4621_, lean_object* v_proof_4622_, uint8_t v_isHEq_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4620_, v_rhs_4621_, v_proof_4622_, v_isHEq_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v___x_4636_; 
lean_dec_ref_known(v___x_4635_, 1);
lean_inc(v_a_4633_);
lean_inc_ref(v_a_4632_);
lean_inc(v_a_4631_);
lean_inc_ref(v_a_4630_);
lean_inc(v_a_4629_);
lean_inc_ref(v_a_4628_);
lean_inc(v_a_4627_);
lean_inc_ref(v_a_4626_);
lean_inc(v_a_4625_);
lean_inc(v_a_4624_);
v___x_4636_ = lean_grind_process_new_facts(v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
return v___x_4636_;
}
else
{
return v___x_4635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4637_, lean_object* v_rhs_4638_, lean_object* v_proof_4639_, lean_object* v_isHEq_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
uint8_t v_isHEq_boxed_4652_; lean_object* v_res_4653_; 
v_isHEq_boxed_4652_ = lean_unbox(v_isHEq_4640_);
v_res_4653_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4637_, v_rhs_4638_, v_proof_4639_, v_isHEq_boxed_4652_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_);
lean_dec(v_a_4650_);
lean_dec_ref(v_a_4649_);
lean_dec(v_a_4648_);
lean_dec_ref(v_a_4647_);
lean_dec(v_a_4646_);
lean_dec_ref(v_a_4645_);
lean_dec(v_a_4644_);
lean_dec_ref(v_a_4643_);
lean_dec(v_a_4642_);
lean_dec(v_a_4641_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4654_, lean_object* v_rhs_4655_, lean_object* v_proof_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
uint8_t v___x_4668_; lean_object* v___x_4669_; 
v___x_4668_ = 0;
v___x_4669_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4654_, v_rhs_4655_, v_proof_4656_, v___x_4668_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4670_, lean_object* v_rhs_4671_, lean_object* v_proof_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4670_, v_rhs_4671_, v_proof_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
lean_dec(v_a_4676_);
lean_dec_ref(v_a_4675_);
lean_dec(v_a_4674_);
lean_dec(v_a_4673_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4685_, lean_object* v_rhs_4686_, lean_object* v_proof_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_){
_start:
{
uint8_t v___x_4699_; lean_object* v___x_4700_; 
v___x_4699_ = 1;
v___x_4700_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4685_, v_rhs_4686_, v_proof_4687_, v___x_4699_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4701_, lean_object* v_rhs_4702_, lean_object* v_proof_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4701_, v_rhs_4702_, v_proof_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_);
lean_dec(v_a_4713_);
lean_dec_ref(v_a_4712_);
lean_dec(v_a_4711_);
lean_dec_ref(v_a_4710_);
lean_dec(v_a_4709_);
lean_dec_ref(v_a_4708_);
lean_dec(v_a_4707_);
lean_dec_ref(v_a_4706_);
lean_dec(v_a_4705_);
lean_dec(v_a_4704_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v___x_4719_; lean_object* v_toGoalState_4720_; lean_object* v_mvarId_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4757_; 
v___x_4719_ = lean_st_ref_take(v_a_4717_);
v_toGoalState_4720_ = lean_ctor_get(v___x_4719_, 0);
v_mvarId_4721_ = lean_ctor_get(v___x_4719_, 1);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4723_ = v___x_4719_;
v_isShared_4724_ = v_isSharedCheck_4757_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_mvarId_4721_);
lean_inc(v_toGoalState_4720_);
lean_dec(v___x_4719_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4757_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v_nextDeclIdx_4725_; lean_object* v_enodeMap_4726_; lean_object* v_exprs_4727_; lean_object* v_parents_4728_; lean_object* v_congrTable_4729_; lean_object* v_appMap_4730_; lean_object* v_indicesFound_4731_; lean_object* v_newFacts_4732_; uint8_t v_inconsistent_4733_; lean_object* v_nextIdx_4734_; lean_object* v_newRawFacts_4735_; lean_object* v_facts_4736_; lean_object* v_extThms_4737_; lean_object* v_ematch_4738_; lean_object* v_inj_4739_; lean_object* v_split_4740_; lean_object* v_clean_4741_; lean_object* v_sstates_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4756_; 
v_nextDeclIdx_4725_ = lean_ctor_get(v_toGoalState_4720_, 0);
v_enodeMap_4726_ = lean_ctor_get(v_toGoalState_4720_, 1);
v_exprs_4727_ = lean_ctor_get(v_toGoalState_4720_, 2);
v_parents_4728_ = lean_ctor_get(v_toGoalState_4720_, 3);
v_congrTable_4729_ = lean_ctor_get(v_toGoalState_4720_, 4);
v_appMap_4730_ = lean_ctor_get(v_toGoalState_4720_, 5);
v_indicesFound_4731_ = lean_ctor_get(v_toGoalState_4720_, 6);
v_newFacts_4732_ = lean_ctor_get(v_toGoalState_4720_, 7);
v_inconsistent_4733_ = lean_ctor_get_uint8(v_toGoalState_4720_, sizeof(void*)*17);
v_nextIdx_4734_ = lean_ctor_get(v_toGoalState_4720_, 8);
v_newRawFacts_4735_ = lean_ctor_get(v_toGoalState_4720_, 9);
v_facts_4736_ = lean_ctor_get(v_toGoalState_4720_, 10);
v_extThms_4737_ = lean_ctor_get(v_toGoalState_4720_, 11);
v_ematch_4738_ = lean_ctor_get(v_toGoalState_4720_, 12);
v_inj_4739_ = lean_ctor_get(v_toGoalState_4720_, 13);
v_split_4740_ = lean_ctor_get(v_toGoalState_4720_, 14);
v_clean_4741_ = lean_ctor_get(v_toGoalState_4720_, 15);
v_sstates_4742_ = lean_ctor_get(v_toGoalState_4720_, 16);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_toGoalState_4720_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4744_ = v_toGoalState_4720_;
v_isShared_4745_ = v_isSharedCheck_4756_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_sstates_4742_);
lean_inc(v_clean_4741_);
lean_inc(v_split_4740_);
lean_inc(v_inj_4739_);
lean_inc(v_ematch_4738_);
lean_inc(v_extThms_4737_);
lean_inc(v_facts_4736_);
lean_inc(v_newRawFacts_4735_);
lean_inc(v_nextIdx_4734_);
lean_inc(v_newFacts_4732_);
lean_inc(v_indicesFound_4731_);
lean_inc(v_appMap_4730_);
lean_inc(v_congrTable_4729_);
lean_inc(v_parents_4728_);
lean_inc(v_exprs_4727_);
lean_inc(v_enodeMap_4726_);
lean_inc(v_nextDeclIdx_4725_);
lean_dec(v_toGoalState_4720_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4756_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4746_; lean_object* v___x_4748_; 
v___x_4746_ = l_Lean_PersistentArray_push___redArg(v_facts_4736_, v_fact_4716_);
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 10, v___x_4746_);
v___x_4748_ = v___x_4744_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_nextDeclIdx_4725_);
lean_ctor_set(v_reuseFailAlloc_4755_, 1, v_enodeMap_4726_);
lean_ctor_set(v_reuseFailAlloc_4755_, 2, v_exprs_4727_);
lean_ctor_set(v_reuseFailAlloc_4755_, 3, v_parents_4728_);
lean_ctor_set(v_reuseFailAlloc_4755_, 4, v_congrTable_4729_);
lean_ctor_set(v_reuseFailAlloc_4755_, 5, v_appMap_4730_);
lean_ctor_set(v_reuseFailAlloc_4755_, 6, v_indicesFound_4731_);
lean_ctor_set(v_reuseFailAlloc_4755_, 7, v_newFacts_4732_);
lean_ctor_set(v_reuseFailAlloc_4755_, 8, v_nextIdx_4734_);
lean_ctor_set(v_reuseFailAlloc_4755_, 9, v_newRawFacts_4735_);
lean_ctor_set(v_reuseFailAlloc_4755_, 10, v___x_4746_);
lean_ctor_set(v_reuseFailAlloc_4755_, 11, v_extThms_4737_);
lean_ctor_set(v_reuseFailAlloc_4755_, 12, v_ematch_4738_);
lean_ctor_set(v_reuseFailAlloc_4755_, 13, v_inj_4739_);
lean_ctor_set(v_reuseFailAlloc_4755_, 14, v_split_4740_);
lean_ctor_set(v_reuseFailAlloc_4755_, 15, v_clean_4741_);
lean_ctor_set(v_reuseFailAlloc_4755_, 16, v_sstates_4742_);
lean_ctor_set_uint8(v_reuseFailAlloc_4755_, sizeof(void*)*17, v_inconsistent_4733_);
v___x_4748_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
lean_object* v___x_4750_; 
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 0, v___x_4748_);
v___x_4750_ = v___x_4723_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4748_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_mvarId_4721_);
v___x_4750_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4751_ = lean_st_ref_set(v_a_4717_, v___x_4750_);
v___x_4752_ = lean_box(0);
v___x_4753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4753_, 0, v___x_4752_);
return v___x_4753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4758_, v_a_4759_);
lean_dec(v_a_4759_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v___x_4774_; 
v___x_4774_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4762_, v_a_4763_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
lean_dec(v_a_4785_);
lean_dec_ref(v_a_4784_);
lean_dec(v_a_4783_);
lean_dec_ref(v_a_4782_);
lean_dec(v_a_4781_);
lean_dec_ref(v_a_4780_);
lean_dec(v_a_4779_);
lean_dec_ref(v_a_4778_);
lean_dec(v_a_4777_);
lean_dec(v_a_4776_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4788_, lean_object* v_rhs_4789_, lean_object* v_proof_4790_, lean_object* v_generation_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v___x_4803_; 
lean_inc_ref(v_rhs_4789_);
lean_inc_ref(v_lhs_4788_);
v___x_4803_ = l_Lean_Meta_mkEq(v_lhs_4788_, v_rhs_4789_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4815_; 
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc_n(v_a_4804_, 2);
lean_dec_ref_known(v___x_4803_, 1);
v___x_4805_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4804_, v_a_4792_);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4815_ == 0)
{
lean_object* v_unused_4816_; 
v_unused_4816_ = lean_ctor_get(v___x_4805_, 0);
lean_dec(v_unused_4816_);
v___x_4807_ = v___x_4805_;
v_isShared_4808_ = v_isSharedCheck_4815_;
goto v_resetjp_4806_;
}
else
{
lean_dec(v___x_4805_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4815_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
lean_ctor_set_tag(v___x_4807_, 1);
lean_ctor_set(v___x_4807_, 0, v_a_4804_);
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4804_);
v___x_4810_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
lean_object* v___x_4811_; 
lean_inc(v_a_4801_);
lean_inc_ref(v_a_4800_);
lean_inc(v_a_4799_);
lean_inc_ref(v_a_4798_);
lean_inc(v_a_4797_);
lean_inc_ref(v_a_4796_);
lean_inc(v_a_4795_);
lean_inc_ref(v_a_4794_);
lean_inc(v_a_4793_);
lean_inc(v_a_4792_);
lean_inc_ref(v___x_4810_);
lean_inc(v_generation_4791_);
lean_inc_ref(v_lhs_4788_);
v___x_4811_ = lean_grind_internalize(v_lhs_4788_, v_generation_4791_, v___x_4810_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_object* v___x_4812_; 
lean_dec_ref_known(v___x_4811_, 1);
lean_inc(v_a_4801_);
lean_inc_ref(v_a_4800_);
lean_inc(v_a_4799_);
lean_inc_ref(v_a_4798_);
lean_inc(v_a_4797_);
lean_inc_ref(v_a_4796_);
lean_inc(v_a_4795_);
lean_inc_ref(v_a_4794_);
lean_inc(v_a_4793_);
lean_inc(v_a_4792_);
lean_inc_ref(v_rhs_4789_);
v___x_4812_ = lean_grind_internalize(v_rhs_4789_, v_generation_4791_, v___x_4810_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v___x_4813_; 
lean_dec_ref_known(v___x_4812_, 1);
v___x_4813_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4788_, v_rhs_4789_, v_proof_4790_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
return v___x_4813_;
}
else
{
lean_dec_ref(v_proof_4790_);
lean_dec_ref(v_rhs_4789_);
lean_dec_ref(v_lhs_4788_);
return v___x_4812_;
}
}
else
{
lean_dec_ref(v___x_4810_);
lean_dec(v_generation_4791_);
lean_dec_ref(v_proof_4790_);
lean_dec_ref(v_rhs_4789_);
lean_dec_ref(v_lhs_4788_);
return v___x_4811_;
}
}
}
}
else
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4824_; 
lean_dec(v_generation_4791_);
lean_dec_ref(v_proof_4790_);
lean_dec_ref(v_rhs_4789_);
lean_dec_ref(v_lhs_4788_);
v_a_4817_ = lean_ctor_get(v___x_4803_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4803_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4819_ = v___x_4803_;
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4803_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4822_; 
if (v_isShared_4820_ == 0)
{
v___x_4822_ = v___x_4819_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4825_, lean_object* v_rhs_4826_, lean_object* v_proof_4827_, lean_object* v_generation_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4825_, v_rhs_4826_, v_proof_4827_, v_generation_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
lean_dec(v_a_4834_);
lean_dec_ref(v_a_4833_);
lean_dec(v_a_4832_);
lean_dec_ref(v_a_4831_);
lean_dec(v_a_4830_);
lean_dec(v_a_4829_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4841_, lean_object* v_generation_4842_, lean_object* v_p_4843_, uint8_t v_isNeg_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_){
_start:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4856_ = lean_box(0);
lean_inc(v_a_4854_);
lean_inc_ref(v_a_4853_);
lean_inc(v_a_4852_);
lean_inc_ref(v_a_4851_);
lean_inc(v_a_4850_);
lean_inc_ref(v_a_4849_);
lean_inc(v_a_4848_);
lean_inc_ref(v_a_4847_);
lean_inc(v_a_4846_);
lean_inc(v_a_4845_);
lean_inc_ref(v_p_4843_);
v___x_4857_ = lean_grind_internalize(v_p_4843_, v_generation_4842_, v___x_4856_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_dec_ref_known(v___x_4857_, 1);
if (v_isNeg_4844_ == 0)
{
lean_object* v___x_4858_; 
v___x_4858_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4849_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; lean_object* v___x_4860_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
lean_inc(v_a_4859_);
lean_dec_ref_known(v___x_4858_, 1);
v___x_4860_ = l_Lean_Meta_mkEqTrue(v_proof_4841_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; lean_object* v___x_4862_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4861_);
lean_dec_ref_known(v___x_4860_, 1);
v___x_4862_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4843_, v_a_4859_, v_a_4861_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_);
return v___x_4862_;
}
else
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
lean_dec(v_a_4859_);
lean_dec_ref(v_p_4843_);
v_a_4863_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4865_ = v___x_4860_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4860_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4866_ == 0)
{
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
else
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4878_; 
lean_dec_ref(v_p_4843_);
lean_dec_ref(v_proof_4841_);
v_a_4871_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4873_ = v___x_4858_;
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4858_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4876_; 
if (v_isShared_4874_ == 0)
{
v___x_4876_ = v___x_4873_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
else
{
lean_object* v___x_4879_; 
v___x_4879_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4849_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v___x_4881_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
lean_inc(v_a_4880_);
lean_dec_ref_known(v___x_4879_, 1);
v___x_4881_ = l_Lean_Meta_mkEqFalse(v_proof_4841_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v_a_4882_; lean_object* v___x_4883_; 
v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
lean_inc(v_a_4882_);
lean_dec_ref_known(v___x_4881_, 1);
v___x_4883_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4843_, v_a_4880_, v_a_4882_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_);
return v___x_4883_;
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
lean_dec(v_a_4880_);
lean_dec_ref(v_p_4843_);
v_a_4884_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4881_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4881_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec_ref(v_p_4843_);
lean_dec_ref(v_proof_4841_);
v_a_4892_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4879_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4879_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4843_);
lean_dec_ref(v_proof_4841_);
return v___x_4857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4900_, lean_object* v_generation_4901_, lean_object* v_p_4902_, lean_object* v_isNeg_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_){
_start:
{
uint8_t v_isNeg_boxed_4915_; lean_object* v_res_4916_; 
v_isNeg_boxed_4915_ = lean_unbox(v_isNeg_4903_);
v_res_4916_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4900_, v_generation_4901_, v_p_4902_, v_isNeg_boxed_4915_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_);
lean_dec(v_a_4913_);
lean_dec_ref(v_a_4912_);
lean_dec(v_a_4911_);
lean_dec_ref(v_a_4910_);
lean_dec(v_a_4909_);
lean_dec_ref(v_a_4908_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
lean_dec(v_a_4905_);
lean_dec(v_a_4904_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4917_, lean_object* v_generation_4918_, lean_object* v_p_4919_, lean_object* v_lhs_4920_, lean_object* v_rhs_4921_, uint8_t v_isNeg_4922_, uint8_t v_isHEq_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_){
_start:
{
if (v_isNeg_4922_ == 0)
{
lean_object* v___x_4935_; lean_object* v___x_4936_; 
lean_inc_ref(v_p_4919_);
v___x_4935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4935_, 0, v_p_4919_);
lean_inc(v_a_4933_);
lean_inc_ref(v_a_4932_);
lean_inc(v_a_4931_);
lean_inc_ref(v_a_4930_);
lean_inc(v_a_4929_);
lean_inc_ref(v_a_4928_);
lean_inc(v_a_4927_);
lean_inc_ref(v_a_4926_);
lean_inc(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v___x_4935_);
lean_inc(v_generation_4918_);
lean_inc_ref(v_lhs_4920_);
v___x_4936_ = lean_grind_internalize(v_lhs_4920_, v_generation_4918_, v___x_4935_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v___x_4937_; 
lean_dec_ref_known(v___x_4936_, 1);
lean_inc(v_a_4933_);
lean_inc_ref(v_a_4932_);
lean_inc(v_a_4931_);
lean_inc_ref(v_a_4930_);
lean_inc(v_a_4929_);
lean_inc_ref(v_a_4928_);
lean_inc(v_a_4927_);
lean_inc_ref(v_a_4926_);
lean_inc(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v_rhs_4921_);
v___x_4937_ = lean_grind_internalize(v_rhs_4921_, v_generation_4918_, v___x_4935_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_object* v___x_4938_; lean_object* v___x_4939_; 
lean_dec_ref_known(v___x_4937_, 1);
v___x_4938_ = lean_box(0);
v___x_4939_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4919_, v___x_4938_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v___x_4940_; 
lean_dec_ref_known(v___x_4939_, 1);
v___x_4940_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4920_, v_rhs_4921_, v_proof_4917_, v_isHEq_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
return v___x_4940_;
}
else
{
lean_dec_ref(v_rhs_4921_);
lean_dec_ref(v_lhs_4920_);
lean_dec_ref(v_proof_4917_);
return v___x_4939_;
}
}
else
{
lean_dec_ref(v_rhs_4921_);
lean_dec_ref(v_lhs_4920_);
lean_dec_ref(v_p_4919_);
lean_dec_ref(v_proof_4917_);
return v___x_4937_;
}
}
else
{
lean_dec_ref_known(v___x_4935_, 1);
lean_dec_ref(v_rhs_4921_);
lean_dec_ref(v_lhs_4920_);
lean_dec_ref(v_p_4919_);
lean_dec(v_generation_4918_);
lean_dec_ref(v_proof_4917_);
return v___x_4936_;
}
}
else
{
lean_object* v___x_4941_; lean_object* v___x_4942_; 
lean_dec_ref(v_rhs_4921_);
lean_dec_ref(v_lhs_4920_);
v___x_4941_ = lean_box(0);
lean_inc(v_a_4933_);
lean_inc_ref(v_a_4932_);
lean_inc(v_a_4931_);
lean_inc_ref(v_a_4930_);
lean_inc(v_a_4929_);
lean_inc_ref(v_a_4928_);
lean_inc(v_a_4927_);
lean_inc_ref(v_a_4926_);
lean_inc(v_a_4925_);
lean_inc(v_a_4924_);
lean_inc_ref(v_p_4919_);
v___x_4942_ = lean_grind_internalize(v_p_4919_, v_generation_4918_, v___x_4941_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
if (lean_obj_tag(v___x_4942_) == 0)
{
lean_object* v___x_4943_; 
lean_dec_ref_known(v___x_4942_, 1);
v___x_4943_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4928_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v_a_4944_; lean_object* v___x_4945_; 
v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
lean_inc(v_a_4944_);
lean_dec_ref_known(v___x_4943_, 1);
v___x_4945_ = l_Lean_Meta_mkEqFalse(v_proof_4917_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
if (lean_obj_tag(v___x_4945_) == 0)
{
lean_object* v_a_4946_; lean_object* v___x_4947_; 
v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
lean_inc(v_a_4946_);
lean_dec_ref_known(v___x_4945_, 1);
v___x_4947_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4919_, v_a_4944_, v_a_4946_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
return v___x_4947_;
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
lean_dec(v_a_4944_);
lean_dec_ref(v_p_4919_);
v_a_4948_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4945_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4945_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
else
{
lean_object* v_a_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4963_; 
lean_dec_ref(v_p_4919_);
lean_dec_ref(v_proof_4917_);
v_a_4956_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4958_ = v___x_4943_;
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_a_4956_);
lean_dec(v___x_4943_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4961_; 
if (v_isShared_4959_ == 0)
{
v___x_4961_ = v___x_4958_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
else
{
lean_dec_ref(v_p_4919_);
lean_dec_ref(v_proof_4917_);
return v___x_4942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4964_ = _args[0];
lean_object* v_generation_4965_ = _args[1];
lean_object* v_p_4966_ = _args[2];
lean_object* v_lhs_4967_ = _args[3];
lean_object* v_rhs_4968_ = _args[4];
lean_object* v_isNeg_4969_ = _args[5];
lean_object* v_isHEq_4970_ = _args[6];
lean_object* v_a_4971_ = _args[7];
lean_object* v_a_4972_ = _args[8];
lean_object* v_a_4973_ = _args[9];
lean_object* v_a_4974_ = _args[10];
lean_object* v_a_4975_ = _args[11];
lean_object* v_a_4976_ = _args[12];
lean_object* v_a_4977_ = _args[13];
lean_object* v_a_4978_ = _args[14];
lean_object* v_a_4979_ = _args[15];
lean_object* v_a_4980_ = _args[16];
lean_object* v_a_4981_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4982_; uint8_t v_isHEq_boxed_4983_; lean_object* v_res_4984_; 
v_isNeg_boxed_4982_ = lean_unbox(v_isNeg_4969_);
v_isHEq_boxed_4983_ = lean_unbox(v_isHEq_4970_);
v_res_4984_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4964_, v_generation_4965_, v_p_4966_, v_lhs_4967_, v_rhs_4968_, v_isNeg_boxed_4982_, v_isHEq_boxed_4983_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_);
lean_dec(v_a_4980_);
lean_dec_ref(v_a_4979_);
lean_dec(v_a_4978_);
lean_dec_ref(v_a_4977_);
lean_dec(v_a_4976_);
lean_dec_ref(v_a_4975_);
lean_dec(v_a_4974_);
lean_dec_ref(v_a_4973_);
lean_dec(v_a_4972_);
lean_dec(v_a_4971_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4988_, lean_object* v_generation_4989_, lean_object* v_p_4990_, uint8_t v_isNeg_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v___x_5003_; 
lean_inc_ref(v_p_4990_);
v___x_5003_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4990_, v_a_4999_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v___x_5005_; uint8_t v___x_5006_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc(v_a_5004_);
lean_dec_ref_known(v___x_5003_, 1);
v___x_5005_ = l_Lean_Expr_cleanupAnnotations(v_a_5004_);
v___x_5006_ = l_Lean_Expr_isApp(v___x_5005_);
if (v___x_5006_ == 0)
{
lean_object* v___x_5007_; 
lean_dec_ref(v___x_5005_);
v___x_5007_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4988_, v_generation_4989_, v_p_4990_, v_isNeg_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
return v___x_5007_;
}
else
{
lean_object* v_arg_5008_; lean_object* v___x_5009_; uint8_t v___x_5010_; 
v_arg_5008_ = lean_ctor_get(v___x_5005_, 1);
lean_inc_ref(v_arg_5008_);
v___x_5009_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5005_);
v___x_5010_ = l_Lean_Expr_isApp(v___x_5009_);
if (v___x_5010_ == 0)
{
lean_object* v___x_5011_; 
lean_dec_ref(v___x_5009_);
lean_dec_ref(v_arg_5008_);
v___x_5011_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4988_, v_generation_4989_, v_p_4990_, v_isNeg_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
return v___x_5011_;
}
else
{
lean_object* v_arg_5012_; lean_object* v___x_5013_; uint8_t v___x_5014_; 
v_arg_5012_ = lean_ctor_get(v___x_5009_, 1);
lean_inc_ref(v_arg_5012_);
v___x_5013_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5009_);
v___x_5014_ = l_Lean_Expr_isApp(v___x_5013_);
if (v___x_5014_ == 0)
{
lean_object* v___x_5015_; 
lean_dec_ref(v___x_5013_);
lean_dec_ref(v_arg_5012_);
lean_dec_ref(v_arg_5008_);
v___x_5015_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4988_, v_generation_4989_, v_p_4990_, v_isNeg_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
return v___x_5015_;
}
else
{
lean_object* v_arg_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; uint8_t v___x_5019_; 
v_arg_5016_ = lean_ctor_get(v___x_5013_, 1);
lean_inc_ref(v_arg_5016_);
v___x_5017_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5013_);
v___x_5018_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5019_ = l_Lean_Expr_isConstOf(v___x_5017_, v___x_5018_);
if (v___x_5019_ == 0)
{
uint8_t v___x_5020_; 
lean_dec_ref(v_arg_5012_);
v___x_5020_ = l_Lean_Expr_isApp(v___x_5017_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; 
lean_dec_ref(v___x_5017_);
lean_dec_ref(v_arg_5016_);
lean_dec_ref(v_arg_5008_);
v___x_5021_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4988_, v_generation_4989_, v_p_4990_, v_isNeg_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
return v___x_5021_;
}
else
{
lean_object* v___x_5022_; lean_object* v___x_5023_; uint8_t v___x_5024_; 
v___x_5022_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5017_);
v___x_5023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5024_ = l_Lean_Expr_isConstOf(v___x_5022_, v___x_5023_);
lean_dec_ref(v___x_5022_);
if (v___x_5024_ == 0)
{
lean_object* v___x_5025_; 
lean_dec_ref(v_arg_5016_);
lean_dec_ref(v_arg_5008_);
v___x_5025_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4988_, v_generation_4989_, v_p_4990_, v_isNeg_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
return v___x_5025_;
}
else
{
lean_object* v___x_5026_; 
v___x_5026_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4988_, v_generation_4989_, v_p_4990_, v_arg_5016_, v_arg_5008_, v_isNeg_4991_, v___x_5024_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
return v___x_5026_;
}
}
}
else
{
uint8_t v___x_5027_; 
lean_dec_ref(v___x_5017_);
v___x_5027_ = l_Lean_Expr_isProp(v_arg_5016_);
lean_dec_ref(v_arg_5016_);
if (v___x_5027_ == 0)
{
lean_object* v___x_5028_; 
v___x_5028_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4988_, v_generation_4989_, v_p_4990_, v_arg_5012_, v_arg_5008_, v_isNeg_4991_, v___x_5027_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
return v___x_5028_;
}
else
{
lean_object* v___x_5029_; 
lean_dec_ref(v_arg_5012_);
lean_dec_ref(v_arg_5008_);
v___x_5029_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4988_, v_generation_4989_, v_p_4990_, v_isNeg_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_);
return v___x_5029_;
}
}
}
}
}
}
else
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5037_; 
lean_dec_ref(v_p_4990_);
lean_dec(v_generation_4989_);
lean_dec_ref(v_proof_4988_);
v_a_5030_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5032_ = v___x_5003_;
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___x_5003_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5035_; 
if (v_isShared_5033_ == 0)
{
v___x_5035_ = v___x_5032_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_a_5030_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5038_, lean_object* v_generation_5039_, lean_object* v_p_5040_, lean_object* v_isNeg_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_){
_start:
{
uint8_t v_isNeg_boxed_5053_; lean_object* v_res_5054_; 
v_isNeg_boxed_5053_ = lean_unbox(v_isNeg_5041_);
v_res_5054_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5038_, v_generation_5039_, v_p_5040_, v_isNeg_boxed_5053_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_);
lean_dec(v_a_5051_);
lean_dec_ref(v_a_5050_);
lean_dec(v_a_5049_);
lean_dec_ref(v_a_5048_);
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v_a_5043_);
lean_dec(v_a_5042_);
return v_res_5054_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5062_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5063_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5064_ = l_Lean_Name_append(v___x_5063_, v___x_5062_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5065_, lean_object* v_proof_5066_, lean_object* v_generation_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_){
_start:
{
lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5093_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v___y_5096_; lean_object* v___y_5097_; lean_object* v___y_5098_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___x_5110_; lean_object* v_options_5111_; uint8_t v_hasTrace_5112_; 
lean_inc_ref(v_fact_5065_);
v___x_5110_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5065_, v_a_5068_);
lean_dec_ref(v___x_5110_);
v_options_5111_ = lean_ctor_get(v_a_5076_, 2);
v_hasTrace_5112_ = lean_ctor_get_uint8(v_options_5111_, sizeof(void*)*1);
if (v_hasTrace_5112_ == 0)
{
v___y_5093_ = v_a_5068_;
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
v___y_5096_ = v_a_5071_;
v___y_5097_ = v_a_5072_;
v___y_5098_ = v_a_5073_;
v___y_5099_ = v_a_5074_;
v___y_5100_ = v_a_5075_;
v___y_5101_ = v_a_5076_;
v___y_5102_ = v_a_5077_;
goto v___jp_5092_;
}
else
{
lean_object* v_inheritedTraceOptions_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; uint8_t v___x_5116_; 
v_inheritedTraceOptions_5113_ = lean_ctor_get(v_a_5076_, 13);
v___x_5114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5115_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5116_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5113_, v_options_5111_, v___x_5115_);
if (v___x_5116_ == 0)
{
v___y_5093_ = v_a_5068_;
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
v___y_5096_ = v_a_5071_;
v___y_5097_ = v_a_5072_;
v___y_5098_ = v_a_5073_;
v___y_5099_ = v_a_5074_;
v___y_5100_ = v_a_5075_;
v___y_5101_ = v_a_5076_;
v___y_5102_ = v_a_5077_;
goto v___jp_5092_;
}
else
{
lean_object* v___x_5117_; 
v___x_5117_ = l_Lean_Meta_Grind_updateLastTag(v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
if (lean_obj_tag(v___x_5117_) == 0)
{
lean_object* v___x_5118_; lean_object* v___x_5119_; 
lean_dec_ref_known(v___x_5117_, 1);
lean_inc_ref(v_fact_5065_);
v___x_5118_ = l_Lean_MessageData_ofExpr(v_fact_5065_);
v___x_5119_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5114_, v___x_5118_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_dec_ref_known(v___x_5119_, 1);
v___y_5093_ = v_a_5068_;
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
v___y_5096_ = v_a_5071_;
v___y_5097_ = v_a_5072_;
v___y_5098_ = v_a_5073_;
v___y_5099_ = v_a_5074_;
v___y_5100_ = v_a_5075_;
v___y_5101_ = v_a_5076_;
v___y_5102_ = v_a_5077_;
goto v___jp_5092_;
}
else
{
lean_dec(v_generation_5067_);
lean_dec_ref(v_proof_5066_);
lean_dec_ref(v_fact_5065_);
return v___x_5119_;
}
}
else
{
lean_dec(v_generation_5067_);
lean_dec_ref(v_proof_5066_);
lean_dec_ref(v_fact_5065_);
return v___x_5117_;
}
}
}
v___jp_5079_:
{
uint8_t v___x_5090_; lean_object* v___x_5091_; 
v___x_5090_ = 0;
v___x_5091_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5066_, v_generation_5067_, v_fact_5065_, v___x_5090_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_);
return v___x_5091_;
}
v___jp_5092_:
{
lean_object* v___x_5103_; uint8_t v___x_5104_; 
lean_inc_ref(v_fact_5065_);
v___x_5103_ = l_Lean_Expr_cleanupAnnotations(v_fact_5065_);
v___x_5104_ = l_Lean_Expr_isApp(v___x_5103_);
if (v___x_5104_ == 0)
{
lean_dec_ref(v___x_5103_);
v___y_5080_ = v___y_5093_;
v___y_5081_ = v___y_5094_;
v___y_5082_ = v___y_5095_;
v___y_5083_ = v___y_5096_;
v___y_5084_ = v___y_5097_;
v___y_5085_ = v___y_5098_;
v___y_5086_ = v___y_5099_;
v___y_5087_ = v___y_5100_;
v___y_5088_ = v___y_5101_;
v___y_5089_ = v___y_5102_;
goto v___jp_5079_;
}
else
{
lean_object* v_arg_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; uint8_t v___x_5108_; 
v_arg_5105_ = lean_ctor_get(v___x_5103_, 1);
lean_inc_ref(v_arg_5105_);
v___x_5106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5103_);
v___x_5107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5108_ = l_Lean_Expr_isConstOf(v___x_5106_, v___x_5107_);
lean_dec_ref(v___x_5106_);
if (v___x_5108_ == 0)
{
lean_dec_ref(v_arg_5105_);
v___y_5080_ = v___y_5093_;
v___y_5081_ = v___y_5094_;
v___y_5082_ = v___y_5095_;
v___y_5083_ = v___y_5096_;
v___y_5084_ = v___y_5097_;
v___y_5085_ = v___y_5098_;
v___y_5086_ = v___y_5099_;
v___y_5087_ = v___y_5100_;
v___y_5088_ = v___y_5101_;
v___y_5089_ = v___y_5102_;
goto v___jp_5079_;
}
else
{
lean_object* v___x_5109_; 
lean_dec_ref(v_fact_5065_);
v___x_5109_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5066_, v_generation_5067_, v_arg_5105_, v___x_5108_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
return v___x_5109_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_){
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
v___x_5154_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5138_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5191_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5157_ = v___x_5154_;
v_isShared_5158_ = v_isSharedCheck_5191_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_dec(v___x_5154_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5191_;
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
if (lean_obj_tag(v_val_5159_) == 0)
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
else
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
}
else
{
lean_object* v___x_5187_; lean_object* v___x_5189_; 
lean_dec(v_a_5155_);
v___x_5187_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5158_ == 0)
{
lean_ctor_set(v___x_5157_, 0, v___x_5187_);
v___x_5189_ = v___x_5157_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___x_5187_);
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
else
{
lean_object* v_a_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5199_; 
v_a_5192_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5199_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5199_ == 0)
{
v___x_5194_ = v___x_5154_;
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_a_5192_);
lean_dec(v___x_5154_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v___x_5197_; 
if (v_isShared_5195_ == 0)
{
v___x_5197_ = v___x_5194_;
goto v_reusejp_5196_;
}
else
{
lean_object* v_reuseFailAlloc_5198_; 
v_reuseFailAlloc_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5198_, 0, v_a_5192_);
v___x_5197_ = v_reuseFailAlloc_5198_;
goto v_reusejp_5196_;
}
v_reusejp_5196_:
{
return v___x_5197_;
}
}
}
}
else
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5207_; 
v_a_5200_ = lean_ctor_get(v___x_5153_, 0);
v_isSharedCheck_5207_ = !lean_is_exclusive(v___x_5153_);
if (v_isSharedCheck_5207_ == 0)
{
v___x_5202_ = v___x_5153_;
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5153_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5207_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v___x_5205_; 
if (v_isShared_5203_ == 0)
{
v___x_5205_ = v___x_5202_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_a_5200_);
v___x_5205_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
return v___x_5205_;
}
}
}
}
else
{
lean_object* v___x_5208_; 
v___x_5208_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5138_);
if (lean_obj_tag(v___x_5208_) == 0)
{
lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5216_; 
v_isSharedCheck_5216_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5216_ == 0)
{
lean_object* v_unused_5217_; 
v_unused_5217_ = lean_ctor_get(v___x_5208_, 0);
lean_dec(v_unused_5217_);
v___x_5210_ = v___x_5208_;
v_isShared_5211_ = v_isSharedCheck_5216_;
goto v_resetjp_5209_;
}
else
{
lean_dec(v___x_5208_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5216_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v___x_5212_; lean_object* v___x_5214_; 
v___x_5212_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5211_ == 0)
{
lean_ctor_set(v___x_5210_, 0, v___x_5212_);
v___x_5214_ = v___x_5210_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v___x_5212_);
v___x_5214_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
return v___x_5214_;
}
}
}
else
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
v_a_5218_ = lean_ctor_get(v___x_5208_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5208_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5220_ = v___x_5208_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5208_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5221_ == 0)
{
v___x_5223_ = v___x_5220_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
}
}
}
else
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5233_; 
v_a_5226_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5228_ = v___x_5149_;
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5149_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5231_; 
if (v_isShared_5229_ == 0)
{
v___x_5231_ = v___x_5228_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
v___x_5231_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
return v___x_5231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v_res_5245_; 
v_res_5245_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
lean_dec(v___y_5237_);
lean_dec_ref(v___y_5236_);
lean_dec(v___y_5235_);
lean_dec(v___y_5234_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_){
_start:
{
lean_object* v___x_5257_; 
v___x_5257_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_);
lean_dec(v_a_5255_);
lean_dec_ref(v_a_5254_);
lean_dec(v_a_5253_);
lean_dec_ref(v_a_5252_);
lean_dec(v_a_5251_);
lean_dec_ref(v_a_5250_);
lean_dec(v_a_5249_);
lean_dec_ref(v_a_5248_);
lean_dec(v_a_5247_);
lean_dec(v_a_5246_);
if (lean_obj_tag(v___x_5257_) == 0)
{
lean_object* v_a_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5271_; 
v_a_5258_ = lean_ctor_get(v___x_5257_, 0);
v_isSharedCheck_5271_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5260_ = v___x_5257_;
v_isShared_5261_ = v_isSharedCheck_5271_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_a_5258_);
lean_dec(v___x_5257_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5271_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v_fst_5262_; 
v_fst_5262_ = lean_ctor_get(v_a_5258_, 0);
lean_inc(v_fst_5262_);
lean_dec(v_a_5258_);
if (lean_obj_tag(v_fst_5262_) == 0)
{
lean_object* v___x_5263_; lean_object* v___x_5265_; 
v___x_5263_ = lean_box(0);
if (v_isShared_5261_ == 0)
{
lean_ctor_set(v___x_5260_, 0, v___x_5263_);
v___x_5265_ = v___x_5260_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5263_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
else
{
lean_object* v_val_5267_; lean_object* v___x_5269_; 
v_val_5267_ = lean_ctor_get(v_fst_5262_, 0);
lean_inc(v_val_5267_);
lean_dec_ref_known(v_fst_5262_, 1);
if (v_isShared_5261_ == 0)
{
lean_ctor_set(v___x_5260_, 0, v_val_5267_);
v___x_5269_ = v___x_5260_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5270_; 
v_reuseFailAlloc_5270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5270_, 0, v_val_5267_);
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
v_a_5272_ = lean_ctor_get(v___x_5257_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5274_ = v___x_5257_;
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5257_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_){
_start:
{
lean_object* v_res_5291_; 
v_res_5291_ = lean_grind_process_new_facts(v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
return v_res_5291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_inst_5292_, lean_object* v_a_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_){
_start:
{
lean_object* v___x_5305_; 
v___x_5305_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_);
return v___x_5305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_inst_5306_, lean_object* v_a_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_){
_start:
{
lean_object* v_res_5319_; 
v_res_5319_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_inst_5306_, v_a_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec(v___y_5315_);
lean_dec_ref(v___y_5314_);
lean_dec(v___y_5313_);
lean_dec_ref(v___y_5312_);
lean_dec(v___y_5311_);
lean_dec_ref(v___y_5310_);
lean_dec(v___y_5309_);
lean_dec(v___y_5308_);
lean_dec_ref(v_a_5307_);
return v_res_5319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5320_, lean_object* v_proof_5321_, lean_object* v_generation_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_){
_start:
{
uint8_t v___x_5334_; 
lean_inc_ref(v_fact_5320_);
v___x_5334_ = l_Lean_Expr_isTrue(v_fact_5320_);
if (v___x_5334_ == 0)
{
lean_object* v___x_5335_; 
v___x_5335_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5323_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5347_; 
v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5338_ = v___x_5335_;
v_isShared_5339_ = v_isSharedCheck_5347_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5335_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5347_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
uint8_t v___x_5340_; 
v___x_5340_ = lean_unbox(v_a_5336_);
lean_dec(v_a_5336_);
if (v___x_5340_ == 0)
{
lean_object* v___x_5341_; lean_object* v___x_5342_; 
lean_del_object(v___x_5338_);
v___x_5341_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5323_);
lean_dec_ref(v___x_5341_);
v___x_5342_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5320_, v_proof_5321_, v_generation_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_);
return v___x_5342_;
}
else
{
lean_object* v___x_5343_; lean_object* v___x_5345_; 
lean_dec(v_generation_5322_);
lean_dec_ref(v_proof_5321_);
lean_dec_ref(v_fact_5320_);
v___x_5343_ = lean_box(0);
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 0, v___x_5343_);
v___x_5345_ = v___x_5338_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5343_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
}
else
{
lean_object* v_a_5348_; lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5355_; 
lean_dec(v_generation_5322_);
lean_dec_ref(v_proof_5321_);
lean_dec_ref(v_fact_5320_);
v_a_5348_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5350_ = v___x_5335_;
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
else
{
lean_inc(v_a_5348_);
lean_dec(v___x_5335_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5355_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5353_; 
if (v_isShared_5351_ == 0)
{
v___x_5353_ = v___x_5350_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_a_5348_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
}
else
{
lean_object* v___x_5356_; lean_object* v___x_5357_; 
lean_dec(v_generation_5322_);
lean_dec_ref(v_proof_5321_);
lean_dec_ref(v_fact_5320_);
v___x_5356_ = lean_box(0);
v___x_5357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5357_, 0, v___x_5356_);
return v___x_5357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5358_, lean_object* v_proof_5359_, lean_object* v_generation_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_){
_start:
{
lean_object* v_res_5372_; 
v_res_5372_ = l_Lean_Meta_Grind_add(v_fact_5358_, v_proof_5359_, v_generation_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_, v_a_5370_);
lean_dec(v_a_5370_);
lean_dec_ref(v_a_5369_);
lean_dec(v_a_5368_);
lean_dec_ref(v_a_5367_);
lean_dec(v_a_5366_);
lean_dec_ref(v_a_5365_);
lean_dec(v_a_5364_);
lean_dec_ref(v_a_5363_);
lean_dec(v_a_5362_);
lean_dec(v_a_5361_);
return v_res_5372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5373_, lean_object* v_generation_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_){
_start:
{
lean_object* v___x_5386_; 
lean_inc(v_fvarId_5373_);
v___x_5386_ = l_Lean_FVarId_getType___redArg(v_fvarId_5373_, v_a_5381_, v_a_5383_, v_a_5384_);
if (lean_obj_tag(v___x_5386_) == 0)
{
lean_object* v_a_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; 
v_a_5387_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_a_5387_);
lean_dec_ref_known(v___x_5386_, 1);
v___x_5388_ = l_Lean_mkFVar(v_fvarId_5373_);
v___x_5389_ = l_Lean_Meta_Grind_add(v_a_5387_, v___x_5388_, v_generation_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_, v_a_5382_, v_a_5383_, v_a_5384_);
return v___x_5389_;
}
else
{
lean_object* v_a_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5397_; 
lean_dec(v_generation_5374_);
lean_dec(v_fvarId_5373_);
v_a_5390_ = lean_ctor_get(v___x_5386_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5392_ = v___x_5386_;
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_a_5390_);
lean_dec(v___x_5386_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5397_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v___x_5395_; 
if (v_isShared_5393_ == 0)
{
v___x_5395_ = v___x_5392_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v_a_5390_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5398_, lean_object* v_generation_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5398_, v_generation_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
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
