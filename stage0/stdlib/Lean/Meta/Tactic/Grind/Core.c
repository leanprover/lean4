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
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 64, 101, 181, 200, 140, 42, 219)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "curr: "};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(v___x_11_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v_self_14_; lean_object* v_next_15_; lean_object* v_root_16_; lean_object* v_congr_17_; lean_object* v_target_x3f_18_; lean_object* v_proof_x3f_19_; uint8_t v_flipped_20_; lean_object* v_size_21_; uint8_t v_interpreted_22_; uint8_t v_ctor_23_; uint8_t v_hasLambdas_24_; uint8_t v_heqProofs_25_; lean_object* v_idx_26_; lean_object* v_generation_27_; lean_object* v_mt_28_; lean_object* v_sTerms_29_; uint8_t v_funCC_30_; lean_object* v_ematchDiagSource_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_54_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_13_);
lean_dec_ref(v___x_12_);
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
lean_dec_ref(v___x_49_);
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
lean_dec_ref(v_entry_290_);
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
lean_dec_ref(v___x_312_);
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
lean_dec_ref(v___x_342_);
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
lean_dec_ref(v___x_457_);
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
lean_dec_ref(v___x_451_);
v___x_452_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_399_);
v___x_453_ = l_Lean_MessageData_ofExpr(v_head_399_);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_448_, v___x_454_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_dec_ref(v___x_455_);
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
lean_dec_ref(v___x_494_);
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
lean_dec_ref(v___x_659_);
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
lean_dec_ref(v___x_642_);
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
lean_dec_ref(v___x_653_);
v___x_654_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_628_);
v___x_655_ = l_Lean_MessageData_ofExpr(v_head_628_);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_650_, v___x_656_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref(v___x_657_);
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
lean_dec_ref(v___x_852_);
v___x_854_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_853_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref(v___x_854_);
v___x_856_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_837_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref(v___x_856_);
v___x_858_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_837_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
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
lean_dec_ref(v___x_994_);
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
lean_dec_ref(v___x_996_);
lean_inc(v_a_995_);
v___x_998_ = l_Lean_Meta_mkDecide(v_a_995_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref(v___x_998_);
v___x_1000_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_987_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref(v___x_1000_);
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
lean_dec_ref(v___x_1073_);
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
lean_dec_ref(v___x_1101_);
v___x_1102_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1070_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_dec_ref(v___x_1102_);
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
lean_dec_ref(v___x_1127_);
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
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1233_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1234_ = l_Lean_Name_append(v___x_1233_, v___x_1232_);
return v___x_1234_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3));
v___x_1237_ = l_Lean_stringToMessageData(v___x_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_lams_1240_, lean_object* v_b_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_fst_1253_; lean_object* v_snd_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1359_; 
v_fst_1253_ = lean_ctor_get(v_b_1241_, 0);
v_snd_1254_ = lean_ctor_get(v_b_1241_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_b_1241_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1256_ = v_b_1241_;
v_isShared_1257_ = v_isSharedCheck_1359_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_snd_1254_);
lean_inc(v_fst_1253_);
lean_dec(v_b_1241_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1359_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v_options_1332_; uint8_t v_hasTrace_1333_; 
v_options_1332_ = lean_ctor_get(v___y_1250_, 2);
v_hasTrace_1333_ = lean_ctor_get_uint8(v_options_1332_, sizeof(void*)*1);
if (v_hasTrace_1333_ == 0)
{
v___y_1301_ = v___y_1242_;
v___y_1302_ = v___y_1243_;
v___y_1303_ = v___y_1244_;
v___y_1304_ = v___y_1245_;
v___y_1305_ = v___y_1246_;
v___y_1306_ = v___y_1247_;
v___y_1307_ = v___y_1248_;
v___y_1308_ = v___y_1249_;
v___y_1309_ = v___y_1250_;
v___y_1310_ = v___y_1251_;
goto v___jp_1300_;
}
else
{
lean_object* v_inheritedTraceOptions_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_inheritedTraceOptions_1334_ = lean_ctor_get(v___y_1250_, 13);
v___x_1335_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1336_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1337_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1334_, v_options_1332_, v___x_1336_);
if (v___x_1337_ == 0)
{
v___y_1301_ = v___y_1242_;
v___y_1302_ = v___y_1243_;
v___y_1303_ = v___y_1244_;
v___y_1304_ = v___y_1245_;
v___y_1305_ = v___y_1246_;
v___y_1306_ = v___y_1247_;
v___y_1307_ = v___y_1248_;
v___y_1308_ = v___y_1249_;
v___y_1309_ = v___y_1250_;
v___y_1310_ = v___y_1251_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Meta_Grind_updateLastTag(v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref(v___x_1338_);
v___x_1339_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4);
lean_inc(v_snd_1254_);
v___x_1340_ = l_Lean_MessageData_ofExpr(v_snd_1254_);
v___x_1341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v___x_1342_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1335_, v___x_1341_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_dec_ref(v___x_1342_);
v___y_1301_ = v___y_1242_;
v___y_1302_ = v___y_1243_;
v___y_1303_ = v___y_1244_;
v___y_1304_ = v___y_1245_;
v___y_1305_ = v___y_1246_;
v___y_1306_ = v___y_1247_;
v___y_1307_ = v___y_1248_;
v___y_1308_ = v___y_1249_;
v___y_1309_ = v___y_1250_;
v___y_1310_ = v___y_1251_;
goto v___jp_1300_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_del_object(v___x_1256_);
lean_dec(v_snd_1254_);
lean_dec(v_fst_1253_);
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_del_object(v___x_1256_);
lean_dec(v_snd_1254_);
lean_dec(v_fst_1253_);
v_a_1351_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1338_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1338_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
v___jp_1258_:
{
if (lean_obj_tag(v_snd_1254_) == 5)
{
lean_object* v_fn_1269_; lean_object* v_arg_1270_; lean_object* v___x_1271_; 
v_fn_1269_ = lean_ctor_get(v_snd_1254_, 0);
lean_inc_ref(v_fn_1269_);
v_arg_1270_ = lean_ctor_get(v_snd_1254_, 1);
lean_inc_ref(v_arg_1270_);
v___x_1271_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1238_, v___y_1259_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = lean_box(0);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc(v___y_1260_);
lean_inc(v___y_1259_);
v___x_1274_ = lean_grind_internalize(v_snd_1254_, v_a_1272_, v___x_1273_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
lean_dec_ref(v___x_1274_);
v___x_1275_ = lean_array_push(v_fst_1253_, v_arg_1270_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_fn_1269_);
lean_ctor_set(v___x_1256_, 0, v___x_1275_);
v___x_1277_ = v___x_1256_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_fn_1269_);
v___x_1277_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
v_b_1241_ = v___x_1277_;
goto _start;
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v_arg_1270_);
lean_dec_ref(v_fn_1269_);
lean_del_object(v___x_1256_);
lean_dec(v_fst_1253_);
v_a_1280_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1274_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1274_);
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
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_arg_1270_);
lean_dec_ref(v_fn_1269_);
lean_dec_ref(v_snd_1254_);
lean_del_object(v___x_1256_);
lean_dec(v_fst_1253_);
v_a_1288_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1271_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1271_);
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
else
{
lean_object* v___x_1297_; 
if (v_isShared_1257_ == 0)
{
v___x_1297_ = v___x_1256_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_fst_1253_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_snd_1254_);
v___x_1297_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
}
v___jp_1300_:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1254_, v_a_1239_, v___y_1301_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; uint8_t v___x_1313_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref(v___x_1311_);
v___x_1313_ = lean_unbox(v_a_1312_);
lean_dec(v_a_1312_);
if (v___x_1313_ == 0)
{
v___y_1259_ = v___y_1301_;
v___y_1260_ = v___y_1302_;
v___y_1261_ = v___y_1303_;
v___y_1262_ = v___y_1304_;
v___y_1263_ = v___y_1305_;
v___y_1264_ = v___y_1306_;
v___y_1265_ = v___y_1307_;
v___y_1266_ = v___y_1308_;
v___y_1267_ = v___y_1309_;
v___y_1268_ = v___y_1310_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_inc(v_fst_1253_);
v___x_1314_ = l_Array_reverse___redArg(v_fst_1253_);
lean_inc(v_snd_1254_);
v___x_1315_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1240_, v_snd_1254_, v___x_1314_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_dec_ref(v___x_1315_);
v___y_1259_ = v___y_1301_;
v___y_1260_ = v___y_1302_;
v___y_1261_ = v___y_1303_;
v___y_1262_ = v___y_1304_;
v___y_1263_ = v___y_1305_;
v___y_1264_ = v___y_1306_;
v___y_1265_ = v___y_1307_;
v___y_1266_ = v___y_1308_;
v___y_1267_ = v___y_1309_;
v___y_1268_ = v___y_1310_;
goto v___jp_1258_;
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_del_object(v___x_1256_);
lean_dec(v_snd_1254_);
lean_dec(v_fst_1253_);
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_del_object(v___x_1256_);
lean_dec(v_snd_1254_);
lean_dec(v_fst_1253_);
v_a_1324_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1311_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1311_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_lams_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1360_, v_a_1361_, v_lams_1362_, v_b_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v_lams_1362_);
lean_dec_ref(v_a_1361_);
lean_dec_ref(v_a_1360_);
return v_res_1375_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1381_, lean_object* v_lams_1382_, lean_object* v_as_x27_1383_, lean_object* v_b_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
if (lean_obj_tag(v_as_x27_1383_) == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_b_1384_);
return v___x_1396_;
}
else
{
lean_object* v_options_1397_; lean_object* v_head_1398_; lean_object* v_tail_1399_; lean_object* v_inheritedTraceOptions_1400_; uint8_t v_hasTrace_1401_; lean_object* v___x_1402_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___x_1426_; uint8_t v_a_1428_; 
v_options_1397_ = lean_ctor_get(v___y_1393_, 2);
v_head_1398_ = lean_ctor_get(v_as_x27_1383_, 0);
v_tail_1399_ = lean_ctor_get(v_as_x27_1383_, 1);
v_inheritedTraceOptions_1400_ = lean_ctor_get(v___y_1393_, 13);
v_hasTrace_1401_ = lean_ctor_get_uint8(v_options_1397_, sizeof(void*)*1);
v___x_1402_ = lean_box(0);
v___x_1426_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
if (v_hasTrace_1401_ == 0)
{
v_a_1428_ = v_hasTrace_1401_;
goto v___jp_1427_;
}
else
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1400_, v_options_1397_, v___x_1435_);
v_a_1428_ = v___x_1436_;
goto v___jp_1427_;
}
v___jp_1403_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_inc(v_head_1398_);
lean_inc_ref(v___y_1404_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___y_1404_);
lean_ctor_set(v___x_1415_, 1, v_head_1398_);
v___x_1416_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_head_1398_, v_a_1381_, v_lams_1382_, v___x_1415_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_dec_ref(v___x_1416_);
v_as_x27_1383_ = v_tail_1399_;
v_b_1384_ = v___x_1402_;
goto _start;
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
v_a_1418_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1416_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1416_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
v___jp_1427_:
{
lean_object* v___x_1429_; 
v___x_1429_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1428_ == 0)
{
v___y_1404_ = v___x_1429_;
v___y_1405_ = v___y_1385_;
v___y_1406_ = v___y_1386_;
v___y_1407_ = v___y_1387_;
v___y_1408_ = v___y_1388_;
v___y_1409_ = v___y_1389_;
v___y_1410_ = v___y_1390_;
v___y_1411_ = v___y_1391_;
v___y_1412_ = v___y_1392_;
v___y_1413_ = v___y_1393_;
v___y_1414_ = v___y_1394_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Meta_Grind_updateLastTag(v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec_ref(v___x_1430_);
v___x_1431_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1398_);
v___x_1432_ = l_Lean_MessageData_ofExpr(v_head_1398_);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1426_, v___x_1433_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref(v___x_1434_);
v___y_1404_ = v___x_1429_;
v___y_1405_ = v___y_1385_;
v___y_1406_ = v___y_1386_;
v___y_1407_ = v___y_1387_;
v___y_1408_ = v___y_1388_;
v___y_1409_ = v___y_1389_;
v___y_1410_ = v___y_1390_;
v___y_1411_ = v___y_1391_;
v___y_1412_ = v___y_1392_;
v___y_1413_ = v___y_1393_;
v___y_1414_ = v___y_1394_;
goto v___jp_1403_;
}
else
{
return v___x_1434_;
}
}
else
{
return v___x_1430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1437_, lean_object* v_lams_1438_, lean_object* v_as_x27_1439_, lean_object* v_b_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1437_, v_lams_1438_, v_as_x27_1439_, v_b_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v_as_x27_1439_);
lean_dec_ref(v_lams_1438_);
lean_dec_ref(v_a_1437_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1453_, lean_object* v_lams_1454_, lean_object* v_as_1455_, lean_object* v_as_x27_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
if (lean_obj_tag(v_as_x27_1456_) == 0)
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_b_1457_);
return v___x_1469_;
}
else
{
lean_object* v_options_1470_; lean_object* v_head_1471_; lean_object* v_tail_1472_; lean_object* v_inheritedTraceOptions_1473_; uint8_t v_hasTrace_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; uint8_t v_a_1501_; 
v_options_1470_ = lean_ctor_get(v___y_1466_, 2);
v_head_1471_ = lean_ctor_get(v_as_x27_1456_, 0);
v_tail_1472_ = lean_ctor_get(v_as_x27_1456_, 1);
v_inheritedTraceOptions_1473_ = lean_ctor_get(v___y_1466_, 13);
v_hasTrace_1474_ = lean_ctor_get_uint8(v_options_1470_, sizeof(void*)*1);
v___x_1475_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1476_ = lean_box(0);
if (v_hasTrace_1474_ == 0)
{
v_a_1501_ = v_hasTrace_1474_;
goto v___jp_1500_;
}
else
{
lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1508_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1509_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1473_, v_options_1470_, v___x_1508_);
v_a_1501_ = v___x_1509_;
goto v___jp_1500_;
}
v___jp_1477_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_inc(v_head_1471_);
lean_inc_ref(v___y_1478_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___y_1478_);
lean_ctor_set(v___x_1489_, 1, v_head_1471_);
v___x_1490_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_head_1471_, v_a_1453_, v_lams_1454_, v___x_1489_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v___x_1491_; 
lean_dec_ref(v___x_1490_);
v___x_1491_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1453_, v_lams_1454_, v_tail_1472_, v___x_1476_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
return v___x_1491_;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
v_a_1492_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1490_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1490_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
v___jp_1500_:
{
lean_object* v___x_1502_; 
v___x_1502_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1501_ == 0)
{
v___y_1478_ = v___x_1502_;
v___y_1479_ = v___y_1458_;
v___y_1480_ = v___y_1459_;
v___y_1481_ = v___y_1460_;
v___y_1482_ = v___y_1461_;
v___y_1483_ = v___y_1462_;
v___y_1484_ = v___y_1463_;
v___y_1485_ = v___y_1464_;
v___y_1486_ = v___y_1465_;
v___y_1487_ = v___y_1466_;
v___y_1488_ = v___y_1467_;
goto v___jp_1477_;
}
else
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Meta_Grind_updateLastTag(v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec_ref(v___x_1503_);
v___x_1504_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1471_);
v___x_1505_ = l_Lean_MessageData_ofExpr(v_head_1471_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1475_, v___x_1506_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_dec_ref(v___x_1507_);
v___y_1478_ = v___x_1502_;
v___y_1479_ = v___y_1458_;
v___y_1480_ = v___y_1459_;
v___y_1481_ = v___y_1460_;
v___y_1482_ = v___y_1461_;
v___y_1483_ = v___y_1462_;
v___y_1484_ = v___y_1463_;
v___y_1485_ = v___y_1464_;
v___y_1486_ = v___y_1465_;
v___y_1487_ = v___y_1466_;
v___y_1488_ = v___y_1467_;
goto v___jp_1477_;
}
else
{
return v___x_1507_;
}
}
else
{
return v___x_1503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1510_, lean_object* v_lams_1511_, lean_object* v_as_1512_, lean_object* v_as_x27_1513_, lean_object* v_b_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1510_, v_lams_1511_, v_as_1512_, v_as_x27_1513_, v_b_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec(v_as_x27_1513_);
lean_dec(v_as_1512_);
lean_dec_ref(v_lams_1511_);
lean_dec_ref(v_a_1510_);
return v_res_1526_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1533_, lean_object* v_lams_1534_, lean_object* v_as_1535_, size_t v_sz_1536_, size_t v_i_1537_, lean_object* v_b_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_usize_dec_lt(v_i_1537_, v_sz_1536_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_b_1538_);
return v___x_1551_;
}
else
{
lean_object* v_options_1552_; lean_object* v_inheritedTraceOptions_1553_; uint8_t v_hasTrace_1554_; lean_object* v___x_1555_; lean_object* v_a_1556_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; 
v_options_1552_ = lean_ctor_get(v___y_1547_, 2);
v_inheritedTraceOptions_1553_ = lean_ctor_get(v___y_1547_, 13);
v_hasTrace_1554_ = lean_ctor_get_uint8(v_options_1552_, sizeof(void*)*1);
v___x_1555_ = lean_box(0);
v_a_1556_ = lean_array_uget_borrowed(v_as_1535_, v_i_1537_);
if (v_hasTrace_1554_ == 0)
{
v___y_1558_ = v___y_1539_;
v___y_1559_ = v___y_1540_;
v___y_1560_ = v___y_1541_;
v___y_1561_ = v___y_1542_;
v___y_1562_ = v___y_1543_;
v___y_1563_ = v___y_1544_;
v___y_1564_ = v___y_1545_;
v___y_1565_ = v___y_1546_;
v___y_1566_ = v___y_1547_;
v___y_1567_ = v___y_1548_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1583_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1584_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1585_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1553_, v_options_1552_, v___x_1584_);
if (v___x_1585_ == 0)
{
v___y_1558_ = v___y_1539_;
v___y_1559_ = v___y_1540_;
v___y_1560_ = v___y_1541_;
v___y_1561_ = v___y_1542_;
v___y_1562_ = v___y_1543_;
v___y_1563_ = v___y_1544_;
v___y_1564_ = v___y_1545_;
v___y_1565_ = v___y_1546_;
v___y_1566_ = v___y_1547_;
v___y_1567_ = v___y_1548_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Meta_Grind_updateLastTag(v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref(v___x_1586_);
v___x_1587_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1556_, v___y_1539_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v___x_1587_);
v___x_1589_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1556_);
v___x_1590_ = l_Lean_MessageData_ofExpr(v_a_1556_);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1588_);
lean_dec(v_a_1588_);
v___x_1595_ = lean_box(0);
v___x_1596_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1594_, v___x_1595_);
v___x_1597_ = l_Lean_MessageData_ofList(v___x_1596_);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1593_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1583_, v___x_1598_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_dec_ref(v___x_1599_);
v___y_1558_ = v___y_1539_;
v___y_1559_ = v___y_1540_;
v___y_1560_ = v___y_1541_;
v___y_1561_ = v___y_1542_;
v___y_1562_ = v___y_1543_;
v___y_1563_ = v___y_1544_;
v___y_1564_ = v___y_1545_;
v___y_1565_ = v___y_1546_;
v___y_1566_ = v___y_1547_;
v___y_1567_ = v___y_1548_;
goto v___jp_1557_;
}
else
{
return v___x_1599_;
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_a_1600_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1587_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1587_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
return v___x_1586_;
}
}
}
v___jp_1557_:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1556_, v___y_1558_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1569_);
lean_dec(v_a_1569_);
v___x_1571_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1533_, v_lams_1534_, v___x_1570_, v___x_1570_, v___x_1555_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___x_1570_);
if (lean_obj_tag(v___x_1571_) == 0)
{
size_t v___x_1572_; size_t v___x_1573_; 
lean_dec_ref(v___x_1571_);
v___x_1572_ = ((size_t)1ULL);
v___x_1573_ = lean_usize_add(v_i_1537_, v___x_1572_);
v_i_1537_ = v___x_1573_;
v_b_1538_ = v___x_1555_;
goto _start;
}
else
{
return v___x_1571_;
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v_a_1575_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1568_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1568_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1608_ = _args[0];
lean_object* v_lams_1609_ = _args[1];
lean_object* v_as_1610_ = _args[2];
lean_object* v_sz_1611_ = _args[3];
lean_object* v_i_1612_ = _args[4];
lean_object* v_b_1613_ = _args[5];
lean_object* v___y_1614_ = _args[6];
lean_object* v___y_1615_ = _args[7];
lean_object* v___y_1616_ = _args[8];
lean_object* v___y_1617_ = _args[9];
lean_object* v___y_1618_ = _args[10];
lean_object* v___y_1619_ = _args[11];
lean_object* v___y_1620_ = _args[12];
lean_object* v___y_1621_ = _args[13];
lean_object* v___y_1622_ = _args[14];
lean_object* v___y_1623_ = _args[15];
lean_object* v___y_1624_ = _args[16];
_start:
{
size_t v_sz_boxed_1625_; size_t v_i_boxed_1626_; lean_object* v_res_1627_; 
v_sz_boxed_1625_ = lean_unbox_usize(v_sz_1611_);
lean_dec(v_sz_1611_);
v_i_boxed_1626_ = lean_unbox_usize(v_i_1612_);
lean_dec(v_i_1612_);
v_res_1627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1608_, v_lams_1609_, v_as_1610_, v_sz_boxed_1625_, v_i_boxed_1626_, v_b_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v_as_1610_);
lean_dec_ref(v_lams_1609_);
lean_dec_ref(v_a_1608_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1628_, lean_object* v_lams_1629_, lean_object* v_as_1630_, size_t v_sz_1631_, size_t v_i_1632_, lean_object* v_b_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_usize_dec_lt(v_i_1632_, v_sz_1631_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_b_1633_);
return v___x_1646_;
}
else
{
lean_object* v_options_1647_; lean_object* v_inheritedTraceOptions_1648_; uint8_t v_hasTrace_1649_; lean_object* v___x_1650_; lean_object* v_a_1651_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; 
v_options_1647_ = lean_ctor_get(v___y_1642_, 2);
v_inheritedTraceOptions_1648_ = lean_ctor_get(v___y_1642_, 13);
v_hasTrace_1649_ = lean_ctor_get_uint8(v_options_1647_, sizeof(void*)*1);
v___x_1650_ = lean_box(0);
v_a_1651_ = lean_array_uget_borrowed(v_as_1630_, v_i_1632_);
if (v_hasTrace_1649_ == 0)
{
v___y_1653_ = v___y_1634_;
v___y_1654_ = v___y_1635_;
v___y_1655_ = v___y_1636_;
v___y_1656_ = v___y_1637_;
v___y_1657_ = v___y_1638_;
v___y_1658_ = v___y_1639_;
v___y_1659_ = v___y_1640_;
v___y_1660_ = v___y_1641_;
v___y_1661_ = v___y_1642_;
v___y_1662_ = v___y_1643_;
goto v___jp_1652_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1678_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1679_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1648_, v_options_1647_, v___x_1679_);
if (v___x_1680_ == 0)
{
v___y_1653_ = v___y_1634_;
v___y_1654_ = v___y_1635_;
v___y_1655_ = v___y_1636_;
v___y_1656_ = v___y_1637_;
v___y_1657_ = v___y_1638_;
v___y_1658_ = v___y_1639_;
v___y_1659_ = v___y_1640_;
v___y_1660_ = v___y_1641_;
v___y_1661_ = v___y_1642_;
v___y_1662_ = v___y_1643_;
goto v___jp_1652_;
}
else
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Meta_Grind_updateLastTag(v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v___x_1682_; 
lean_dec_ref(v___x_1681_);
v___x_1682_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1651_, v___y_1634_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref(v___x_1682_);
v___x_1684_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1651_);
v___x_1685_ = l_Lean_MessageData_ofExpr(v_a_1651_);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1683_);
lean_dec(v_a_1683_);
v___x_1690_ = lean_box(0);
v___x_1691_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1689_, v___x_1690_);
v___x_1692_ = l_Lean_MessageData_ofList(v___x_1691_);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1688_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1678_, v___x_1693_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_dec_ref(v___x_1694_);
v___y_1653_ = v___y_1634_;
v___y_1654_ = v___y_1635_;
v___y_1655_ = v___y_1636_;
v___y_1656_ = v___y_1637_;
v___y_1657_ = v___y_1638_;
v___y_1658_ = v___y_1639_;
v___y_1659_ = v___y_1640_;
v___y_1660_ = v___y_1641_;
v___y_1661_ = v___y_1642_;
v___y_1662_ = v___y_1643_;
goto v___jp_1652_;
}
else
{
return v___x_1694_;
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
v_a_1695_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1682_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1682_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
return v___x_1681_;
}
}
}
v___jp_1652_:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1651_, v___y_1653_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1664_);
lean_dec(v_a_1664_);
v___x_1666_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1628_, v_lams_1629_, v___x_1665_, v___x_1665_, v___x_1650_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___x_1665_);
if (lean_obj_tag(v___x_1666_) == 0)
{
size_t v___x_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
lean_dec_ref(v___x_1666_);
v___x_1667_ = ((size_t)1ULL);
v___x_1668_ = lean_usize_add(v_i_1632_, v___x_1667_);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1628_, v_lams_1629_, v_as_1630_, v_sz_1631_, v___x_1668_, v___x_1650_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1669_;
}
else
{
return v___x_1666_;
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1670_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1663_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1663_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1703_ = _args[0];
lean_object* v_lams_1704_ = _args[1];
lean_object* v_as_1705_ = _args[2];
lean_object* v_sz_1706_ = _args[3];
lean_object* v_i_1707_ = _args[4];
lean_object* v_b_1708_ = _args[5];
lean_object* v___y_1709_ = _args[6];
lean_object* v___y_1710_ = _args[7];
lean_object* v___y_1711_ = _args[8];
lean_object* v___y_1712_ = _args[9];
lean_object* v___y_1713_ = _args[10];
lean_object* v___y_1714_ = _args[11];
lean_object* v___y_1715_ = _args[12];
lean_object* v___y_1716_ = _args[13];
lean_object* v___y_1717_ = _args[14];
lean_object* v___y_1718_ = _args[15];
lean_object* v___y_1719_ = _args[16];
_start:
{
size_t v_sz_boxed_1720_; size_t v_i_boxed_1721_; lean_object* v_res_1722_; 
v_sz_boxed_1720_ = lean_unbox_usize(v_sz_1706_);
lean_dec(v_sz_1706_);
v_i_boxed_1721_ = lean_unbox_usize(v_i_1707_);
lean_dec(v_i_1707_);
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1703_, v_lams_1704_, v_as_1705_, v_sz_boxed_1720_, v_i_boxed_1721_, v_b_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v_as_1705_);
lean_dec_ref(v_lams_1704_);
lean_dec_ref(v_a_1703_);
return v_res_1722_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1725_ = l_Lean_stringToMessageData(v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1729_, lean_object* v_fns_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1742_ = lean_array_get_size(v_lams_1729_);
v___x_1743_ = lean_unsigned_to_nat(0u);
v___x_1744_ = lean_nat_dec_eq(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1745_ = lean_st_ref_get(v_a_1731_);
v___x_1746_ = l_Lean_instInhabitedExpr;
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_nat_sub(v___x_1742_, v___x_1747_);
v___x_1749_ = lean_array_get_borrowed(v___x_1746_, v_lams_1729_, v___x_1748_);
lean_dec(v___x_1748_);
lean_inc(v___x_1749_);
v___x_1750_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1745_, v___x_1749_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
lean_dec(v___x_1745_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v_options_1775_; uint8_t v_hasTrace_1776_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
v_options_1775_ = lean_ctor_get(v_a_1739_, 2);
v_hasTrace_1776_ = lean_ctor_get_uint8(v_options_1775_, sizeof(void*)*1);
if (v_hasTrace_1776_ == 0)
{
v___y_1753_ = v_a_1731_;
v___y_1754_ = v_a_1732_;
v___y_1755_ = v_a_1733_;
v___y_1756_ = v_a_1734_;
v___y_1757_ = v_a_1735_;
v___y_1758_ = v_a_1736_;
v___y_1759_ = v_a_1737_;
v___y_1760_ = v_a_1738_;
v___y_1761_ = v_a_1739_;
v___y_1762_ = v_a_1740_;
goto v___jp_1752_;
}
else
{
lean_object* v_inheritedTraceOptions_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_inheritedTraceOptions_1777_ = lean_ctor_get(v_a_1739_, 13);
v___x_1778_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1779_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1780_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1777_, v_options_1775_, v___x_1779_);
if (v___x_1780_ == 0)
{
v___y_1753_ = v_a_1731_;
v___y_1754_ = v_a_1732_;
v___y_1755_ = v_a_1733_;
v___y_1756_ = v_a_1734_;
v___y_1757_ = v_a_1735_;
v___y_1758_ = v_a_1736_;
v___y_1759_ = v_a_1737_;
v___y_1760_ = v_a_1738_;
v___y_1761_ = v_a_1739_;
v___y_1762_ = v_a_1740_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Meta_Grind_updateLastTag(v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec_ref(v___x_1781_);
v___x_1782_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1730_);
v___x_1783_ = lean_array_to_list(v_fns_1730_);
v___x_1784_ = lean_box(0);
v___x_1785_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1783_, v___x_1784_);
v___x_1786_ = l_Lean_MessageData_ofList(v___x_1785_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1782_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
lean_inc_ref(v_lams_1729_);
v___x_1790_ = lean_array_to_list(v_lams_1729_);
v___x_1791_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1790_, v___x_1784_);
v___x_1792_ = l_Lean_MessageData_ofList(v___x_1791_);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1789_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1778_, v___x_1793_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_dec_ref(v___x_1794_);
v___y_1753_ = v_a_1731_;
v___y_1754_ = v_a_1732_;
v___y_1755_ = v_a_1733_;
v___y_1756_ = v_a_1734_;
v___y_1757_ = v_a_1735_;
v___y_1758_ = v_a_1736_;
v___y_1759_ = v_a_1737_;
v___y_1760_ = v_a_1738_;
v___y_1761_ = v_a_1739_;
v___y_1762_ = v_a_1740_;
goto v___jp_1752_;
}
else
{
lean_dec(v_a_1751_);
lean_dec_ref(v_fns_1730_);
lean_dec_ref(v_lams_1729_);
return v___x_1794_;
}
}
else
{
lean_dec(v_a_1751_);
lean_dec_ref(v_fns_1730_);
lean_dec_ref(v_lams_1729_);
return v___x_1781_;
}
}
}
v___jp_1752_:
{
lean_object* v___x_1763_; size_t v_sz_1764_; size_t v___x_1765_; lean_object* v___x_1766_; 
v___x_1763_ = lean_box(0);
v_sz_1764_ = lean_array_size(v_fns_1730_);
v___x_1765_ = ((size_t)0ULL);
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1751_, v_lams_1729_, v_fns_1730_, v_sz_1764_, v___x_1765_, v___x_1763_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec_ref(v_fns_1730_);
lean_dec_ref(v_lams_1729_);
lean_dec(v_a_1751_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v___x_1766_, 0);
lean_dec(v_unused_1774_);
v___x_1768_ = v___x_1766_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v___x_1766_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1763_);
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1763_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
else
{
return v___x_1766_;
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec_ref(v_fns_1730_);
lean_dec_ref(v_lams_1729_);
v_a_1795_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1750_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1750_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec_ref(v_fns_1730_);
lean_dec_ref(v_lams_1729_);
v___x_1803_ = lean_box(0);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1805_, lean_object* v_fns_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1805_, v_fns_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec(v_a_1807_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1819_, lean_object* v_lams_1820_, lean_object* v_as_1821_, lean_object* v_as_x27_1822_, lean_object* v_b_1823_, lean_object* v_a_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1819_, v_lams_1820_, v_as_1821_, v_as_x27_1822_, v_b_1823_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1837_ = _args[0];
lean_object* v_lams_1838_ = _args[1];
lean_object* v_as_1839_ = _args[2];
lean_object* v_as_x27_1840_ = _args[3];
lean_object* v_b_1841_ = _args[4];
lean_object* v_a_1842_ = _args[5];
lean_object* v___y_1843_ = _args[6];
lean_object* v___y_1844_ = _args[7];
lean_object* v___y_1845_ = _args[8];
lean_object* v___y_1846_ = _args[9];
lean_object* v___y_1847_ = _args[10];
lean_object* v___y_1848_ = _args[11];
lean_object* v___y_1849_ = _args[12];
lean_object* v___y_1850_ = _args[13];
lean_object* v___y_1851_ = _args[14];
lean_object* v___y_1852_ = _args[15];
lean_object* v___y_1853_ = _args[16];
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1837_, v_lams_1838_, v_as_1839_, v_as_x27_1840_, v_b_1841_, v_a_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v_as_x27_1840_);
lean_dec(v_as_1839_);
lean_dec_ref(v_lams_1838_);
lean_dec_ref(v_a_1837_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1855_, lean_object* v_lams_1856_, lean_object* v_as_1857_, lean_object* v_as_x27_1858_, lean_object* v_b_1859_, lean_object* v_a_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1855_, v_lams_1856_, v_as_x27_1858_, v_b_1859_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1873_ = _args[0];
lean_object* v_lams_1874_ = _args[1];
lean_object* v_as_1875_ = _args[2];
lean_object* v_as_x27_1876_ = _args[3];
lean_object* v_b_1877_ = _args[4];
lean_object* v_a_1878_ = _args[5];
lean_object* v___y_1879_ = _args[6];
lean_object* v___y_1880_ = _args[7];
lean_object* v___y_1881_ = _args[8];
lean_object* v___y_1882_ = _args[9];
lean_object* v___y_1883_ = _args[10];
lean_object* v___y_1884_ = _args[11];
lean_object* v___y_1885_ = _args[12];
lean_object* v___y_1886_ = _args[13];
lean_object* v___y_1887_ = _args[14];
lean_object* v___y_1888_ = _args[15];
lean_object* v___y_1889_ = _args[16];
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1873_, v_lams_1874_, v_as_1875_, v_as_x27_1876_, v_b_1877_, v_a_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec(v_as_x27_1876_);
lean_dec(v_as_1875_);
lean_dec_ref(v_lams_1874_);
lean_dec_ref(v_a_1873_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1894_, lean_object* v_as_1895_, size_t v_sz_1896_, size_t v_i_1897_, lean_object* v_b_1898_){
_start:
{
lean_object* v_a_1900_; uint8_t v___x_1904_; 
v___x_1904_ = lean_usize_dec_lt(v_i_1897_, v_sz_1896_);
if (v___x_1904_ == 0)
{
lean_inc_ref(v_b_1898_);
return v_b_1898_;
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_a_1907_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1907_ = lean_array_uget_borrowed(v_as_1895_, v_i_1897_);
if (lean_obj_tag(v_a_1907_) == 6)
{
lean_object* v_binderType_1908_; uint8_t v___x_1909_; 
v_binderType_1908_ = lean_ctor_get(v_a_1907_, 1);
v___x_1909_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_d_1894_, v_binderType_1908_);
if (v___x_1909_ == 0)
{
v_a_1900_ = v___x_1906_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_inc_ref(v_a_1907_);
v___x_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1910_, 0, v_a_1907_);
v___x_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v___x_1905_);
return v___x_1912_;
}
}
else
{
v_a_1900_ = v___x_1906_;
goto v___jp_1899_;
}
}
v___jp_1899_:
{
size_t v___x_1901_; size_t v___x_1902_; 
v___x_1901_ = ((size_t)1ULL);
v___x_1902_ = lean_usize_add(v_i_1897_, v___x_1901_);
v_i_1897_ = v___x_1902_;
v_b_1898_ = v_a_1900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_1913_, lean_object* v_as_1914_, lean_object* v_sz_1915_, lean_object* v_i_1916_, lean_object* v_b_1917_){
_start:
{
size_t v_sz_boxed_1918_; size_t v_i_boxed_1919_; lean_object* v_res_1920_; 
v_sz_boxed_1918_ = lean_unbox_usize(v_sz_1915_);
lean_dec(v_sz_1915_);
v_i_boxed_1919_ = lean_unbox_usize(v_i_1916_);
lean_dec(v_i_1916_);
v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1913_, v_as_1914_, v_sz_boxed_1918_, v_i_boxed_1919_, v_b_1917_);
lean_dec_ref(v_b_1917_);
lean_dec_ref(v_as_1914_);
lean_dec_ref(v_d_1913_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_1921_, lean_object* v_d_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; size_t v_sz_1925_; size_t v___x_1926_; lean_object* v___x_1927_; lean_object* v_fst_1928_; 
v___x_1923_ = lean_box(0);
v___x_1924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_1925_ = lean_array_size(v_lams_1921_);
v___x_1926_ = ((size_t)0ULL);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1922_, v_lams_1921_, v_sz_1925_, v___x_1926_, v___x_1924_);
v_fst_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_fst_1928_);
lean_dec_ref(v___x_1927_);
if (lean_obj_tag(v_fst_1928_) == 0)
{
return v___x_1923_;
}
else
{
lean_object* v_val_1929_; 
v_val_1929_ = lean_ctor_get(v_fst_1928_, 0);
lean_inc(v_val_1929_);
lean_dec_ref(v_fst_1928_);
return v_val_1929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_1930_, lean_object* v_d_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_1930_, v_d_1931_);
lean_dec_ref(v_d_1931_);
lean_dec_ref(v_lams_1930_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_1943_, lean_object* v_lams_u2081_1944_, lean_object* v_as_1945_, size_t v_sz_1946_, size_t v_i_1947_, lean_object* v_b_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_a_1961_; uint8_t v___x_1965_; 
v___x_1965_ = lean_usize_dec_lt(v_i_1947_, v_sz_1946_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_b_1948_);
return v___x_1966_;
}
else
{
lean_object* v___x_1967_; lean_object* v_a_1968_; 
v___x_1967_ = lean_box(0);
v_a_1968_ = lean_array_uget_borrowed(v_as_1945_, v_i_1947_);
if (lean_obj_tag(v_a_1968_) == 6)
{
lean_object* v_binderType_1969_; lean_object* v_body_1970_; lean_object* v___x_1971_; 
v_binderType_1969_ = lean_ctor_get(v_a_1968_, 1);
v_body_1970_ = lean_ctor_get(v_a_1968_, 2);
lean_inc_ref(v_binderType_1969_);
v___x_1971_ = l_Lean_Meta_getLevel(v_binderType_1969_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_1974_ = lean_box(0);
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_a_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
lean_inc_ref(v___x_1975_);
v___x_1976_ = l_Lean_mkConst(v___x_1973_, v___x_1975_);
lean_inc_ref(v_binderType_1969_);
v___x_1977_ = l_Lean_Expr_app___override(v___x_1976_, v_binderType_1969_);
v___x_1978_ = lean_box(0);
v___x_1979_ = l_Lean_Meta_synthInstance_x3f(v___x_1977_, v___x_1978_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1979_);
if (lean_obj_tag(v_a_1980_) == 1)
{
lean_object* v_val_1981_; lean_object* v___x_1982_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; uint8_t v___x_2047_; 
v_val_1981_ = lean_ctor_get(v_a_1980_, 0);
lean_inc(v_val_1981_);
lean_dec_ref(v_a_1980_);
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_2047_ = l_Lean_Expr_hasLooseBVars(v_body_1970_);
if (v___x_2047_ == 0)
{
v___y_1984_ = v___y_1949_;
v___y_1985_ = v___y_1950_;
v___y_1986_ = v___y_1951_;
v___y_1987_ = v___y_1952_;
v___y_1988_ = v___y_1953_;
v___y_1989_ = v___y_1954_;
v___y_1990_ = v___y_1955_;
v___y_1991_ = v___y_1956_;
v___y_1992_ = v___y_1957_;
v___y_1993_ = v___y_1958_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_1975_);
v___x_2049_ = l_Lean_mkConst(v___x_2048_, v___x_1975_);
lean_inc_ref(v_binderType_1969_);
v___x_2050_ = l_Lean_Expr_app___override(v___x_2049_, v_binderType_1969_);
v___x_2051_ = l_Lean_Meta_synthInstance_x3f(v___x_2050_, v___x_1978_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
if (lean_obj_tag(v_a_2052_) == 0)
{
lean_dec(v_val_1981_);
lean_dec_ref(v___x_1975_);
v_a_1961_ = v___x_1967_;
goto v___jp_1960_;
}
else
{
lean_dec_ref(v_a_2052_);
if (v___x_2047_ == 0)
{
lean_dec(v_val_1981_);
lean_dec_ref(v___x_1975_);
v_a_1961_ = v___x_1967_;
goto v___jp_1960_;
}
else
{
v___y_1984_ = v___y_1949_;
v___y_1985_ = v___y_1950_;
v___y_1986_ = v___y_1951_;
v___y_1987_ = v___y_1952_;
v___y_1988_ = v___y_1953_;
v___y_1989_ = v___y_1954_;
v___y_1990_ = v___y_1955_;
v___y_1991_ = v___y_1956_;
v___y_1992_ = v___y_1957_;
v___y_1993_ = v___y_1958_;
goto v___jp_1983_;
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_val_1981_);
lean_dec_ref(v___x_1975_);
v_a_2053_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2051_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2051_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
v___jp_1983_:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_1943_, v_binderType_1969_);
if (lean_obj_tag(v___x_1994_) == 1)
{
lean_object* v_val_1995_; 
v_val_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_val_1995_);
lean_dec_ref(v___x_1994_);
if (lean_obj_tag(v_val_1995_) == 6)
{
lean_object* v_binderType_1996_; lean_object* v_body_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v_binderType_1996_ = lean_ctor_get(v_val_1995_, 1);
lean_inc_ref(v_binderType_1996_);
v_body_1997_ = lean_ctor_get(v_val_1995_, 2);
lean_inc_ref(v_body_1997_);
lean_dec_ref(v_val_1995_);
v___x_1998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_1999_ = l_Lean_mkConst(v___x_1998_, v___x_1975_);
v___x_2000_ = l_Lean_mkAppB(v___x_1999_, v_binderType_1996_, v_val_1981_);
v___x_2001_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2000_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref(v___x_2001_);
v___x_2003_ = lean_array_fget_borrowed(v_lams_u2081_1944_, v___x_1982_);
v___x_2004_ = lean_array_fget_borrowed(v_lams_u2082_1943_, v___x_1982_);
lean_inc(v___y_1993_);
lean_inc_ref(v___y_1992_);
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
lean_inc(v___y_1985_);
lean_inc(v___y_1984_);
lean_inc(v___x_2004_);
lean_inc(v___x_2003_);
v___x_2005_ = lean_grind_mk_eq_proof(v___x_2003_, v___x_2004_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v___x_2005_);
v___x_2007_ = lean_expr_instantiate1(v_body_1970_, v_a_2002_);
v___x_2008_ = lean_expr_instantiate1(v_body_1997_, v_a_2002_);
lean_dec_ref(v_body_1997_);
v___x_2009_ = l_Lean_Meta_mkCongrFun(v_a_2006_, v_a_2002_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2011_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = l_Lean_Meta_mkEq(v___x_2007_, v___x_2008_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref(v___x_2011_);
v___x_2013_ = l_Lean_Meta_mkExpectedPropHint(v_a_2010_, v_a_2012_);
v___x_2014_ = l_Lean_Meta_Grind_pushNewFact(v___x_2013_, v___x_1982_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_dec_ref(v___x_2014_);
v_a_1961_ = v___x_1967_;
goto v___jp_1960_;
}
else
{
return v___x_2014_;
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_a_2010_);
v_a_2015_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2011_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2011_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v___x_2008_);
lean_dec_ref(v___x_2007_);
v_a_2023_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2009_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2009_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_a_2002_);
lean_dec_ref(v_body_1997_);
v_a_2031_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2005_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2005_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v_body_1997_);
v_a_2039_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2001_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2001_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
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
else
{
lean_dec(v_val_1995_);
lean_dec(v_val_1981_);
lean_dec_ref(v___x_1975_);
v_a_1961_ = v___x_1967_;
goto v___jp_1960_;
}
}
else
{
lean_dec(v___x_1994_);
lean_dec(v_val_1981_);
lean_dec_ref(v___x_1975_);
v_a_1961_ = v___x_1967_;
goto v___jp_1960_;
}
}
}
else
{
lean_dec(v_a_1980_);
lean_dec_ref(v___x_1975_);
v_a_1961_ = v___x_1967_;
goto v___jp_1960_;
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref(v___x_1975_);
v_a_2061_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_1979_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_1979_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v_a_2069_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_1971_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_1971_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
v_a_1961_ = v___x_1967_;
goto v___jp_1960_;
}
}
v___jp_1960_:
{
size_t v___x_1962_; size_t v___x_1963_; 
v___x_1962_ = ((size_t)1ULL);
v___x_1963_ = lean_usize_add(v_i_1947_, v___x_1962_);
v_i_1947_ = v___x_1963_;
v_b_1948_ = v_a_1961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2077_ = _args[0];
lean_object* v_lams_u2081_2078_ = _args[1];
lean_object* v_as_2079_ = _args[2];
lean_object* v_sz_2080_ = _args[3];
lean_object* v_i_2081_ = _args[4];
lean_object* v_b_2082_ = _args[5];
lean_object* v___y_2083_ = _args[6];
lean_object* v___y_2084_ = _args[7];
lean_object* v___y_2085_ = _args[8];
lean_object* v___y_2086_ = _args[9];
lean_object* v___y_2087_ = _args[10];
lean_object* v___y_2088_ = _args[11];
lean_object* v___y_2089_ = _args[12];
lean_object* v___y_2090_ = _args[13];
lean_object* v___y_2091_ = _args[14];
lean_object* v___y_2092_ = _args[15];
lean_object* v___y_2093_ = _args[16];
_start:
{
size_t v_sz_boxed_2094_; size_t v_i_boxed_2095_; lean_object* v_res_2096_; 
v_sz_boxed_2094_ = lean_unbox_usize(v_sz_2080_);
lean_dec(v_sz_2080_);
v_i_boxed_2095_ = lean_unbox_usize(v_i_2081_);
lean_dec(v_i_2081_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2077_, v_lams_u2081_2078_, v_as_2079_, v_sz_boxed_2094_, v_i_boxed_2095_, v_b_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v_as_2079_);
lean_dec_ref(v_lams_u2081_2078_);
lean_dec_ref(v_lams_u2082_2077_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2097_, lean_object* v_lams_u2082_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2110_ = lean_array_get_size(v_lams_u2081_2097_);
v___x_2111_ = lean_unsigned_to_nat(0u);
v___x_2112_ = lean_nat_dec_eq(v___x_2110_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = lean_array_get_size(v_lams_u2082_2098_);
v___x_2114_ = lean_nat_dec_eq(v___x_2113_, v___x_2111_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; size_t v_sz_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
v___x_2115_ = lean_box(0);
v_sz_2116_ = lean_array_size(v_lams_u2081_2097_);
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2098_, v_lams_u2081_2097_, v_lams_u2081_2097_, v_sz_2116_, v___x_2117_, v___x_2115_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; 
v_unused_2126_ = lean_ctor_get(v___x_2118_, 0);
lean_dec(v_unused_2126_);
v___x_2120_ = v___x_2118_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_dec(v___x_2118_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2115_);
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2115_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
else
{
return v___x_2118_;
}
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_box(0);
v___x_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
return v___x_2130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2131_, lean_object* v_lams_u2082_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2131_, v_lams_u2082_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec_ref(v_lams_u2082_2132_);
lean_dec_ref(v_lams_u2081_2131_);
return v_res_2144_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2145_){
_start:
{
uint8_t v___x_2146_; 
v___x_2146_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2147_){
_start:
{
uint8_t v_res_2148_; lean_object* v_r_2149_; 
v_res_2148_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2147_);
lean_dec_ref(v_x_2147_);
v_r_2149_ = lean_box(v_res_2148_);
return v_r_2149_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2150_, lean_object* v_x_2151_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2153_, lean_object* v_x_2154_){
_start:
{
uint8_t v_res_2155_; lean_object* v_r_2156_; 
v_res_2155_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2153_, v_x_2154_);
lean_dec_ref(v_x_2154_);
v_r_2156_ = lean_box(v_res_2155_);
return v_r_2156_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2157_, lean_object* v_v_2158_, lean_object* v_i_2159_){
_start:
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = lean_array_get_size(v_xs_2157_);
v___x_2161_ = lean_nat_dec_lt(v_i_2159_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; 
lean_dec(v_i_2159_);
v___x_2162_ = lean_box(0);
return v___x_2162_;
}
else
{
lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2163_ = lean_array_fget_borrowed(v_xs_2157_, v_i_2159_);
v___x_2164_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2163_, v_v_2158_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_unsigned_to_nat(1u);
v___x_2166_ = lean_nat_add(v_i_2159_, v___x_2165_);
lean_dec(v_i_2159_);
v_i_2159_ = v___x_2166_;
goto _start;
}
else
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_i_2159_);
return v___x_2168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2169_, lean_object* v_v_2170_, lean_object* v_i_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2169_, v_v_2170_, v_i_2171_);
lean_dec_ref(v_v_2170_);
lean_dec_ref(v_xs_2169_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2173_, lean_object* v_v_2174_){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2173_, v_v_2174_, v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2177_, lean_object* v_v_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2177_, v_v_2178_);
lean_dec_ref(v_v_2178_);
lean_dec_ref(v_xs_2177_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2180_, size_t v_x_2181_, lean_object* v_x_2182_){
_start:
{
if (lean_obj_tag(v_x_2180_) == 0)
{
lean_object* v_es_2183_; lean_object* v___x_2184_; size_t v___x_2185_; size_t v___x_2186_; size_t v___x_2187_; lean_object* v_j_2188_; lean_object* v_entry_2189_; 
v_es_2183_ = lean_ctor_get(v_x_2180_, 0);
v___x_2184_ = lean_box(2);
v___x_2185_ = ((size_t)5ULL);
v___x_2186_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2187_ = lean_usize_land(v_x_2181_, v___x_2186_);
v_j_2188_ = lean_usize_to_nat(v___x_2187_);
v_entry_2189_ = lean_array_get(v___x_2184_, v_es_2183_, v_j_2188_);
switch(lean_obj_tag(v_entry_2189_))
{
case 0:
{
lean_object* v_key_2190_; uint8_t v___x_2191_; 
v_key_2190_ = lean_ctor_get(v_entry_2189_, 0);
lean_inc(v_key_2190_);
lean_dec_ref(v_entry_2189_);
v___x_2191_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2182_, v_key_2190_);
lean_dec(v_key_2190_);
if (v___x_2191_ == 0)
{
lean_dec(v_j_2188_);
return v_x_2180_;
}
else
{
lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2199_; 
lean_inc_ref(v_es_2183_);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_x_2180_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v_x_2180_, 0);
lean_dec(v_unused_2200_);
v___x_2193_ = v_x_2180_;
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
else
{
lean_dec(v_x_2180_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2199_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = lean_array_set(v_es_2183_, v_j_2188_, v___x_2184_);
lean_dec(v_j_2188_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2195_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
case 1:
{
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2234_; 
lean_inc_ref(v_es_2183_);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_x_2180_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v_x_2180_, 0);
lean_dec(v_unused_2235_);
v___x_2202_ = v_x_2180_;
v_isShared_2203_ = v_isSharedCheck_2234_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v_x_2180_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2234_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_node_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2233_; 
v_node_2204_ = lean_ctor_get(v_entry_2189_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_entry_2189_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2206_ = v_entry_2189_;
v_isShared_2207_ = v_isSharedCheck_2233_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_node_2204_);
lean_dec(v_entry_2189_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2233_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v_entries_2208_; size_t v___x_2209_; lean_object* v_newNode_2210_; lean_object* v___x_2211_; 
v_entries_2208_ = lean_array_set(v_es_2183_, v_j_2188_, v___x_2184_);
v___x_2209_ = lean_usize_shift_right(v_x_2181_, v___x_2185_);
v_newNode_2210_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2204_, v___x_2209_, v_x_2182_);
lean_inc_ref(v_newNode_2210_);
v___x_2211_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2210_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v___x_2213_; 
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v_newNode_2210_);
v___x_2213_ = v___x_2206_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_newNode_2210_);
v___x_2213_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = lean_array_set(v_entries_2208_, v_j_2188_, v___x_2213_);
lean_dec(v_j_2188_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2214_);
v___x_2216_ = v___x_2202_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
else
{
lean_object* v_val_2219_; lean_object* v_fst_2220_; lean_object* v_snd_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v_newNode_2210_);
lean_del_object(v___x_2206_);
v_val_2219_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_val_2219_);
lean_dec_ref(v___x_2211_);
v_fst_2220_ = lean_ctor_get(v_val_2219_, 0);
v_snd_2221_ = lean_ctor_get(v_val_2219_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_val_2219_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2223_ = v_val_2219_;
v_isShared_2224_ = v_isSharedCheck_2232_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_snd_2221_);
lean_inc(v_fst_2220_);
lean_dec(v_val_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2232_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_fst_2220_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_snd_2221_);
v___x_2226_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = lean_array_set(v_entries_2208_, v_j_2188_, v___x_2226_);
lean_dec(v_j_2188_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2227_);
v___x_2229_ = v___x_2202_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2188_);
return v_x_2180_;
}
}
}
else
{
lean_object* v_ks_2236_; lean_object* v_vs_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2251_; 
v_ks_2236_ = lean_ctor_get(v_x_2180_, 0);
v_vs_2237_ = lean_ctor_get(v_x_2180_, 1);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_x_2180_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2239_ = v_x_2180_;
v_isShared_2240_ = v_isSharedCheck_2251_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_vs_2237_);
lean_inc(v_ks_2236_);
lean_dec(v_x_2180_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2251_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2236_, v_x_2182_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v___x_2243_; 
if (v_isShared_2240_ == 0)
{
v___x_2243_ = v___x_2239_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_ks_2236_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_vs_2237_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
else
{
lean_object* v_val_2245_; lean_object* v_keys_x27_2246_; lean_object* v_vals_x27_2247_; lean_object* v___x_2249_; 
v_val_2245_ = lean_ctor_get(v___x_2241_, 0);
lean_inc_n(v_val_2245_, 2);
lean_dec_ref(v___x_2241_);
v_keys_x27_2246_ = l_Array_eraseIdx___redArg(v_ks_2236_, v_val_2245_);
v_vals_x27_2247_ = l_Array_eraseIdx___redArg(v_vs_2237_, v_val_2245_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 1, v_vals_x27_2247_);
lean_ctor_set(v___x_2239_, 0, v_keys_x27_2246_);
v___x_2249_ = v___x_2239_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_keys_x27_2246_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_vals_x27_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2252_, lean_object* v_x_2253_, lean_object* v_x_2254_){
_start:
{
size_t v_x_21947__boxed_2255_; lean_object* v_res_2256_; 
v_x_21947__boxed_2255_ = lean_unbox_usize(v_x_2253_);
lean_dec(v_x_2253_);
v_res_2256_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2252_, v_x_21947__boxed_2255_, v_x_2254_);
lean_dec_ref(v_x_2254_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2257_, lean_object* v_x_2258_){
_start:
{
uint64_t v___x_2259_; size_t v_h_2260_; lean_object* v___x_2261_; 
v___x_2259_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2258_);
v_h_2260_ = lean_uint64_to_usize(v___x_2259_);
v___x_2261_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2257_, v_h_2260_, v_x_2258_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2262_, lean_object* v_x_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2262_, v_x_2263_);
lean_dec_ref(v_x_2263_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
if (lean_obj_tag(v_as_2265_) == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_box(0);
v___x_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
return v___x_2278_;
}
else
{
lean_object* v_head_2279_; lean_object* v_tail_2280_; lean_object* v___x_2281_; 
v_head_2279_ = lean_ctor_get(v_as_2265_, 0);
lean_inc(v_head_2279_);
v_tail_2280_ = lean_ctor_get(v_as_2265_, 1);
lean_inc(v_tail_2280_);
lean_dec_ref(v_as_2265_);
v___x_2281_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2279_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_dec_ref(v___x_2281_);
v_as_2265_ = v_tail_2280_;
goto _start;
}
else
{
lean_dec(v_tail_2280_);
return v___x_2281_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec(v___y_2284_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2296_, lean_object* v_vals_2297_, lean_object* v_i_2298_, lean_object* v_k_2299_){
_start:
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = lean_array_get_size(v_keys_2296_);
v___x_2301_ = lean_nat_dec_lt(v_i_2298_, v___x_2300_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; 
lean_dec(v_i_2298_);
v___x_2302_ = lean_box(0);
return v___x_2302_;
}
else
{
lean_object* v_k_x27_2303_; uint8_t v___x_2304_; 
v_k_x27_2303_ = lean_array_fget_borrowed(v_keys_2296_, v_i_2298_);
v___x_2304_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_2299_, v_k_x27_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = lean_unsigned_to_nat(1u);
v___x_2306_ = lean_nat_add(v_i_2298_, v___x_2305_);
lean_dec(v_i_2298_);
v_i_2298_ = v___x_2306_;
goto _start;
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_array_fget_borrowed(v_vals_2297_, v_i_2298_);
lean_dec(v_i_2298_);
lean_inc(v___x_2308_);
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2310_, lean_object* v_vals_2311_, lean_object* v_i_2312_, lean_object* v_k_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2310_, v_vals_2311_, v_i_2312_, v_k_2313_);
lean_dec_ref(v_k_2313_);
lean_dec_ref(v_vals_2311_);
lean_dec_ref(v_keys_2310_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2315_, size_t v_x_2316_, lean_object* v_x_2317_){
_start:
{
if (lean_obj_tag(v_x_2315_) == 0)
{
lean_object* v_es_2318_; lean_object* v___x_2319_; size_t v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; lean_object* v_j_2323_; lean_object* v___x_2324_; 
v_es_2318_ = lean_ctor_get(v_x_2315_, 0);
v___x_2319_ = lean_box(2);
v___x_2320_ = ((size_t)5ULL);
v___x_2321_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2322_ = lean_usize_land(v_x_2316_, v___x_2321_);
v_j_2323_ = lean_usize_to_nat(v___x_2322_);
v___x_2324_ = lean_array_get_borrowed(v___x_2319_, v_es_2318_, v_j_2323_);
lean_dec(v_j_2323_);
switch(lean_obj_tag(v___x_2324_))
{
case 0:
{
lean_object* v_key_2325_; lean_object* v_val_2326_; uint8_t v___x_2327_; 
v_key_2325_ = lean_ctor_get(v___x_2324_, 0);
v_val_2326_ = lean_ctor_get(v___x_2324_, 1);
v___x_2327_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2317_, v_key_2325_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_box(0);
return v___x_2328_;
}
else
{
lean_object* v___x_2329_; 
lean_inc(v_val_2326_);
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v_val_2326_);
return v___x_2329_;
}
}
case 1:
{
lean_object* v_node_2330_; size_t v___x_2331_; 
v_node_2330_ = lean_ctor_get(v___x_2324_, 0);
v___x_2331_ = lean_usize_shift_right(v_x_2316_, v___x_2320_);
v_x_2315_ = v_node_2330_;
v_x_2316_ = v___x_2331_;
goto _start;
}
default: 
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_box(0);
return v___x_2333_;
}
}
}
else
{
lean_object* v_ks_2334_; lean_object* v_vs_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_ks_2334_ = lean_ctor_get(v_x_2315_, 0);
v_vs_2335_ = lean_ctor_get(v_x_2315_, 1);
v___x_2336_ = lean_unsigned_to_nat(0u);
v___x_2337_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2334_, v_vs_2335_, v___x_2336_, v_x_2317_);
return v___x_2337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
size_t v_x_22166__boxed_2341_; lean_object* v_res_2342_; 
v_x_22166__boxed_2341_ = lean_unbox_usize(v_x_2339_);
lean_dec(v_x_2339_);
v_res_2342_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2338_, v_x_22166__boxed_2341_, v_x_2340_);
lean_dec_ref(v_x_2340_);
lean_dec_ref(v_x_2338_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
uint64_t v___x_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2344_);
v___x_2346_ = lean_uint64_to_usize(v___x_2345_);
v___x_2347_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2343_, v___x_2346_, v_x_2344_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2348_, v_x_2349_);
lean_dec_ref(v_x_2349_);
lean_dec_ref(v_x_2348_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2351_, lean_object* v_b_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
if (lean_obj_tag(v_as_x27_2351_) == 0)
{
lean_object* v___x_2364_; 
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v_b_2352_);
return v___x_2364_;
}
else
{
lean_object* v_head_2365_; lean_object* v_tail_2366_; lean_object* v___x_2367_; lean_object* v_toGoalState_2368_; lean_object* v_ematch_2369_; lean_object* v_delayedThmInsts_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v_head_2365_ = lean_ctor_get(v_as_x27_2351_, 0);
v_tail_2366_ = lean_ctor_get(v_as_x27_2351_, 1);
v___x_2367_ = lean_st_ref_get(v___y_2353_);
v_toGoalState_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc_ref(v_toGoalState_2368_);
lean_dec(v___x_2367_);
v_ematch_2369_ = lean_ctor_get(v_toGoalState_2368_, 12);
lean_inc_ref(v_ematch_2369_);
lean_dec_ref(v_toGoalState_2368_);
v_delayedThmInsts_2370_ = lean_ctor_get(v_ematch_2369_, 10);
lean_inc_ref(v_delayedThmInsts_2370_);
lean_dec_ref(v_ematch_2369_);
v___x_2371_ = lean_box(0);
v___x_2372_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2370_, v_head_2365_);
lean_dec_ref(v_delayedThmInsts_2370_);
if (lean_obj_tag(v___x_2372_) == 1)
{
lean_object* v_val_2373_; lean_object* v___x_2374_; lean_object* v_toGoalState_2375_; lean_object* v_ematch_2376_; lean_object* v_mvarId_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2431_; 
v_val_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_val_2373_);
lean_dec_ref(v___x_2372_);
v___x_2374_ = lean_st_ref_take(v___y_2353_);
v_toGoalState_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc_ref(v_toGoalState_2375_);
v_ematch_2376_ = lean_ctor_get(v_toGoalState_2375_, 12);
lean_inc_ref(v_ematch_2376_);
v_mvarId_2377_ = lean_ctor_get(v___x_2374_, 1);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2431_ == 0)
{
lean_object* v_unused_2432_; 
v_unused_2432_ = lean_ctor_get(v___x_2374_, 0);
lean_dec(v_unused_2432_);
v___x_2379_ = v___x_2374_;
v_isShared_2380_ = v_isSharedCheck_2431_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_mvarId_2377_);
lean_dec(v___x_2374_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2431_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_nextDeclIdx_2381_; lean_object* v_enodeMap_2382_; lean_object* v_exprs_2383_; lean_object* v_parents_2384_; lean_object* v_congrTable_2385_; lean_object* v_appMap_2386_; lean_object* v_indicesFound_2387_; lean_object* v_newFacts_2388_; uint8_t v_inconsistent_2389_; lean_object* v_nextIdx_2390_; lean_object* v_newRawFacts_2391_; lean_object* v_facts_2392_; lean_object* v_extThms_2393_; lean_object* v_inj_2394_; lean_object* v_split_2395_; lean_object* v_clean_2396_; lean_object* v_sstates_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2429_; 
v_nextDeclIdx_2381_ = lean_ctor_get(v_toGoalState_2375_, 0);
v_enodeMap_2382_ = lean_ctor_get(v_toGoalState_2375_, 1);
v_exprs_2383_ = lean_ctor_get(v_toGoalState_2375_, 2);
v_parents_2384_ = lean_ctor_get(v_toGoalState_2375_, 3);
v_congrTable_2385_ = lean_ctor_get(v_toGoalState_2375_, 4);
v_appMap_2386_ = lean_ctor_get(v_toGoalState_2375_, 5);
v_indicesFound_2387_ = lean_ctor_get(v_toGoalState_2375_, 6);
v_newFacts_2388_ = lean_ctor_get(v_toGoalState_2375_, 7);
v_inconsistent_2389_ = lean_ctor_get_uint8(v_toGoalState_2375_, sizeof(void*)*17);
v_nextIdx_2390_ = lean_ctor_get(v_toGoalState_2375_, 8);
v_newRawFacts_2391_ = lean_ctor_get(v_toGoalState_2375_, 9);
v_facts_2392_ = lean_ctor_get(v_toGoalState_2375_, 10);
v_extThms_2393_ = lean_ctor_get(v_toGoalState_2375_, 11);
v_inj_2394_ = lean_ctor_get(v_toGoalState_2375_, 13);
v_split_2395_ = lean_ctor_get(v_toGoalState_2375_, 14);
v_clean_2396_ = lean_ctor_get(v_toGoalState_2375_, 15);
v_sstates_2397_ = lean_ctor_get(v_toGoalState_2375_, 16);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_toGoalState_2375_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v_toGoalState_2375_, 12);
lean_dec(v_unused_2430_);
v___x_2399_ = v_toGoalState_2375_;
v_isShared_2400_ = v_isSharedCheck_2429_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_sstates_2397_);
lean_inc(v_clean_2396_);
lean_inc(v_split_2395_);
lean_inc(v_inj_2394_);
lean_inc(v_extThms_2393_);
lean_inc(v_facts_2392_);
lean_inc(v_newRawFacts_2391_);
lean_inc(v_nextIdx_2390_);
lean_inc(v_newFacts_2388_);
lean_inc(v_indicesFound_2387_);
lean_inc(v_appMap_2386_);
lean_inc(v_congrTable_2385_);
lean_inc(v_parents_2384_);
lean_inc(v_exprs_2383_);
lean_inc(v_enodeMap_2382_);
lean_inc(v_nextDeclIdx_2381_);
lean_dec(v_toGoalState_2375_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2429_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_thmMap_2401_; lean_object* v_gmt_2402_; lean_object* v_thms_2403_; lean_object* v_newThms_2404_; lean_object* v_numInstances_2405_; lean_object* v_numDelayedInstances_2406_; lean_object* v_num_2407_; lean_object* v_preInstances_2408_; lean_object* v_nextThmIdx_2409_; lean_object* v_matchEqNames_2410_; lean_object* v_delayedThmInsts_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2428_; 
v_thmMap_2401_ = lean_ctor_get(v_ematch_2376_, 0);
v_gmt_2402_ = lean_ctor_get(v_ematch_2376_, 1);
v_thms_2403_ = lean_ctor_get(v_ematch_2376_, 2);
v_newThms_2404_ = lean_ctor_get(v_ematch_2376_, 3);
v_numInstances_2405_ = lean_ctor_get(v_ematch_2376_, 4);
v_numDelayedInstances_2406_ = lean_ctor_get(v_ematch_2376_, 5);
v_num_2407_ = lean_ctor_get(v_ematch_2376_, 6);
v_preInstances_2408_ = lean_ctor_get(v_ematch_2376_, 7);
v_nextThmIdx_2409_ = lean_ctor_get(v_ematch_2376_, 8);
v_matchEqNames_2410_ = lean_ctor_get(v_ematch_2376_, 9);
v_delayedThmInsts_2411_ = lean_ctor_get(v_ematch_2376_, 10);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_ematch_2376_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2413_ = v_ematch_2376_;
v_isShared_2414_ = v_isSharedCheck_2428_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_delayedThmInsts_2411_);
lean_inc(v_matchEqNames_2410_);
lean_inc(v_nextThmIdx_2409_);
lean_inc(v_preInstances_2408_);
lean_inc(v_num_2407_);
lean_inc(v_numDelayedInstances_2406_);
lean_inc(v_numInstances_2405_);
lean_inc(v_newThms_2404_);
lean_inc(v_thms_2403_);
lean_inc(v_gmt_2402_);
lean_inc(v_thmMap_2401_);
lean_dec(v_ematch_2376_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2428_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2415_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2411_, v_head_2365_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 10, v___x_2415_);
v___x_2417_ = v___x_2413_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_thmMap_2401_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_gmt_2402_);
lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_thms_2403_);
lean_ctor_set(v_reuseFailAlloc_2427_, 3, v_newThms_2404_);
lean_ctor_set(v_reuseFailAlloc_2427_, 4, v_numInstances_2405_);
lean_ctor_set(v_reuseFailAlloc_2427_, 5, v_numDelayedInstances_2406_);
lean_ctor_set(v_reuseFailAlloc_2427_, 6, v_num_2407_);
lean_ctor_set(v_reuseFailAlloc_2427_, 7, v_preInstances_2408_);
lean_ctor_set(v_reuseFailAlloc_2427_, 8, v_nextThmIdx_2409_);
lean_ctor_set(v_reuseFailAlloc_2427_, 9, v_matchEqNames_2410_);
lean_ctor_set(v_reuseFailAlloc_2427_, 10, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2419_; 
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 12, v___x_2417_);
v___x_2419_ = v___x_2399_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_nextDeclIdx_2381_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_enodeMap_2382_);
lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_exprs_2383_);
lean_ctor_set(v_reuseFailAlloc_2426_, 3, v_parents_2384_);
lean_ctor_set(v_reuseFailAlloc_2426_, 4, v_congrTable_2385_);
lean_ctor_set(v_reuseFailAlloc_2426_, 5, v_appMap_2386_);
lean_ctor_set(v_reuseFailAlloc_2426_, 6, v_indicesFound_2387_);
lean_ctor_set(v_reuseFailAlloc_2426_, 7, v_newFacts_2388_);
lean_ctor_set(v_reuseFailAlloc_2426_, 8, v_nextIdx_2390_);
lean_ctor_set(v_reuseFailAlloc_2426_, 9, v_newRawFacts_2391_);
lean_ctor_set(v_reuseFailAlloc_2426_, 10, v_facts_2392_);
lean_ctor_set(v_reuseFailAlloc_2426_, 11, v_extThms_2393_);
lean_ctor_set(v_reuseFailAlloc_2426_, 12, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2426_, 13, v_inj_2394_);
lean_ctor_set(v_reuseFailAlloc_2426_, 14, v_split_2395_);
lean_ctor_set(v_reuseFailAlloc_2426_, 15, v_clean_2396_);
lean_ctor_set(v_reuseFailAlloc_2426_, 16, v_sstates_2397_);
lean_ctor_set_uint8(v_reuseFailAlloc_2426_, sizeof(void*)*17, v_inconsistent_2389_);
v___x_2419_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2421_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2419_);
v___x_2421_ = v___x_2379_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_mvarId_2377_);
v___x_2421_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_st_ref_set(v___y_2353_, v___x_2421_);
v___x_2423_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2373_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_dec_ref(v___x_2423_);
v_as_x27_2351_ = v_tail_2366_;
v_b_2352_ = v___x_2371_;
goto _start;
}
else
{
return v___x_2423_;
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
lean_dec(v___x_2372_);
v_as_x27_2351_ = v_tail_2366_;
v_b_2352_ = v___x_2371_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2434_, lean_object* v_b_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2434_, v_b_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec(v_as_x27_2434_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2449_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2489_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2489_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2489_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
uint8_t v___x_2465_; 
v___x_2465_ = lean_unbox(v_a_2461_);
lean_dec(v_a_2461_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v_toGoalState_2467_; lean_object* v_ematch_2468_; lean_object* v_delayedThmInsts_2469_; uint8_t v___x_2470_; 
v___x_2466_ = lean_st_ref_get(v_a_2449_);
v_toGoalState_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc_ref(v_toGoalState_2467_);
lean_dec(v___x_2466_);
v_ematch_2468_ = lean_ctor_get(v_toGoalState_2467_, 12);
lean_inc_ref(v_ematch_2468_);
lean_dec_ref(v_toGoalState_2467_);
v_delayedThmInsts_2469_ = lean_ctor_get(v_ematch_2468_, 10);
lean_inc_ref(v_delayedThmInsts_2469_);
lean_dec_ref(v_ematch_2468_);
v___x_2470_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2469_);
lean_dec_ref(v_delayedThmInsts_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
lean_del_object(v___x_2463_);
v___x_2471_ = lean_box(0);
v___x_2472_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2448_, v___x_2471_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2472_, 0);
lean_dec(v_unused_2480_);
v___x_2474_ = v___x_2472_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_dec(v___x_2472_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2471_);
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2471_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
else
{
return v___x_2472_;
}
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = lean_box(0);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2481_);
v___x_2483_ = v___x_2463_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2485_ = lean_box(0);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2485_);
v___x_2487_ = v___x_2463_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_a_2490_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2460_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2460_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec(v_toPropagateDown_2498_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2511_, lean_object* v_x_2512_, lean_object* v_x_2513_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2512_, v_x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2515_, lean_object* v_x_2516_, lean_object* v_x_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2515_, v_x_2516_, v_x_2517_);
lean_dec_ref(v_x_2517_);
lean_dec_ref(v_x_2516_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2520_, v_x_2521_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2523_, lean_object* v_x_2524_, lean_object* v_x_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2523_, v_x_2524_, v_x_2525_);
lean_dec_ref(v_x_2525_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2527_, lean_object* v_as_x27_2528_, lean_object* v_b_2529_, lean_object* v_a_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2528_, v_b_2529_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2543_, lean_object* v_as_x27_2544_, lean_object* v_b_2545_, lean_object* v_a_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2543_, v_as_x27_2544_, v_b_2545_, v_a_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec(v_as_x27_2544_);
lean_dec(v_as_2543_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2559_, lean_object* v_x_2560_, size_t v_x_2561_, lean_object* v_x_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2560_, v_x_2561_, v_x_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2564_, lean_object* v_x_2565_, lean_object* v_x_2566_, lean_object* v_x_2567_){
_start:
{
size_t v_x_22463__boxed_2568_; lean_object* v_res_2569_; 
v_x_22463__boxed_2568_ = lean_unbox_usize(v_x_2566_);
lean_dec(v_x_2566_);
v_res_2569_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2564_, v_x_2565_, v_x_22463__boxed_2568_, v_x_2567_);
lean_dec_ref(v_x_2567_);
lean_dec_ref(v_x_2565_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2570_, lean_object* v_x_2571_, size_t v_x_2572_, lean_object* v_x_2573_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2571_, v_x_2572_, v_x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2575_, lean_object* v_x_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_){
_start:
{
size_t v_x_22474__boxed_2579_; lean_object* v_res_2580_; 
v_x_22474__boxed_2579_ = lean_unbox_usize(v_x_2577_);
lean_dec(v_x_2577_);
v_res_2580_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2575_, v_x_2576_, v_x_22474__boxed_2579_, v_x_2578_);
lean_dec_ref(v_x_2578_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2581_, lean_object* v_keys_2582_, lean_object* v_vals_2583_, lean_object* v_heq_2584_, lean_object* v_i_2585_, lean_object* v_k_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2582_, v_vals_2583_, v_i_2585_, v_k_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2588_, lean_object* v_keys_2589_, lean_object* v_vals_2590_, lean_object* v_heq_2591_, lean_object* v_i_2592_, lean_object* v_k_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2588_, v_keys_2589_, v_vals_2590_, v_heq_2591_, v_i_2592_, v_k_2593_);
lean_dec_ref(v_k_2593_);
lean_dec_ref(v_vals_2590_);
lean_dec_ref(v_keys_2589_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2595_, lean_object* v_keys_2596_, lean_object* v_vals_2597_, lean_object* v_i_2598_, lean_object* v_k_2599_){
_start:
{
lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2600_ = lean_array_get_size(v_keys_2596_);
v___x_2601_ = lean_nat_dec_lt(v_i_2598_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
lean_dec_ref(v_k_2599_);
lean_dec(v_i_2598_);
v___x_2602_ = lean_box(0);
return v___x_2602_;
}
else
{
lean_object* v_k_x27_2603_; uint8_t v___x_2604_; 
v_k_x27_2603_ = lean_array_fget_borrowed(v_keys_2596_, v_i_2598_);
lean_inc(v_k_x27_2603_);
lean_inc_ref(v_k_2599_);
v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2595_, v_k_2599_, v_k_x27_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_unsigned_to_nat(1u);
v___x_2606_ = lean_nat_add(v_i_2598_, v___x_2605_);
lean_dec(v_i_2598_);
v_i_2598_ = v___x_2606_;
goto _start;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec_ref(v_k_2599_);
v___x_2608_ = lean_array_fget_borrowed(v_vals_2597_, v_i_2598_);
lean_dec(v_i_2598_);
lean_inc(v___x_2608_);
lean_inc(v_k_x27_2603_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_k_x27_2603_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2611_, lean_object* v_keys_2612_, lean_object* v_vals_2613_, lean_object* v_i_2614_, lean_object* v_k_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2611_, v_keys_2612_, v_vals_2613_, v_i_2614_, v_k_2615_);
lean_dec_ref(v_vals_2613_);
lean_dec_ref(v_keys_2612_);
lean_dec_ref(v___x_2611_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2617_, lean_object* v_x_2618_, size_t v_x_2619_, lean_object* v_x_2620_){
_start:
{
if (lean_obj_tag(v_x_2618_) == 0)
{
lean_object* v_es_2621_; lean_object* v___x_2622_; size_t v___x_2623_; size_t v___x_2624_; size_t v___x_2625_; lean_object* v_j_2626_; lean_object* v___x_2627_; 
v_es_2621_ = lean_ctor_get(v_x_2618_, 0);
lean_inc_ref(v_es_2621_);
lean_dec_ref(v_x_2618_);
v___x_2622_ = lean_box(2);
v___x_2623_ = ((size_t)5ULL);
v___x_2624_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2625_ = lean_usize_land(v_x_2619_, v___x_2624_);
v_j_2626_ = lean_usize_to_nat(v___x_2625_);
v___x_2627_ = lean_array_get(v___x_2622_, v_es_2621_, v_j_2626_);
lean_dec(v_j_2626_);
lean_dec_ref(v_es_2621_);
switch(lean_obj_tag(v___x_2627_))
{
case 0:
{
lean_object* v_key_2628_; lean_object* v_val_2629_; uint8_t v___x_2630_; 
v_key_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc_n(v_key_2628_, 2);
v_val_2629_ = lean_ctor_get(v___x_2627_, 1);
lean_inc(v_val_2629_);
lean_dec_ref(v___x_2627_);
v___x_2630_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2617_, v_x_2620_, v_key_2628_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
lean_dec(v_val_2629_);
lean_dec(v_key_2628_);
v___x_2631_ = lean_box(0);
return v___x_2631_;
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2632_, 0, v_key_2628_);
lean_ctor_set(v___x_2632_, 1, v_val_2629_);
v___x_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
return v___x_2633_;
}
}
case 1:
{
lean_object* v_node_2634_; size_t v___x_2635_; 
v_node_2634_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_node_2634_);
lean_dec_ref(v___x_2627_);
v___x_2635_ = lean_usize_shift_right(v_x_2619_, v___x_2623_);
v_x_2618_ = v_node_2634_;
v_x_2619_ = v___x_2635_;
goto _start;
}
default: 
{
lean_object* v___x_2637_; 
lean_dec_ref(v_x_2620_);
v___x_2637_ = lean_box(0);
return v___x_2637_;
}
}
}
else
{
lean_object* v_ks_2638_; lean_object* v_vs_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_ks_2638_ = lean_ctor_get(v_x_2618_, 0);
lean_inc_ref(v_ks_2638_);
v_vs_2639_ = lean_ctor_get(v_x_2618_, 1);
lean_inc_ref(v_vs_2639_);
lean_dec_ref(v_x_2618_);
v___x_2640_ = lean_unsigned_to_nat(0u);
v___x_2641_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2617_, v_ks_2638_, v_vs_2639_, v___x_2640_, v_x_2620_);
lean_dec_ref(v_vs_2639_);
lean_dec_ref(v_ks_2638_);
return v___x_2641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_){
_start:
{
size_t v_x_27643__boxed_2646_; lean_object* v_res_2647_; 
v_x_27643__boxed_2646_ = lean_unbox_usize(v_x_2644_);
lean_dec(v_x_2644_);
v_res_2647_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2642_, v_x_2643_, v_x_27643__boxed_2646_, v_x_2645_);
lean_dec_ref(v___x_2642_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2648_, lean_object* v_x_2649_, lean_object* v_x_2650_){
_start:
{
uint64_t v___x_2651_; size_t v___x_2652_; lean_object* v___x_2653_; 
lean_inc_ref(v_x_2650_);
v___x_2651_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2648_, v_x_2650_);
v___x_2652_ = lean_uint64_to_usize(v___x_2651_);
lean_inc_ref(v_x_2649_);
v___x_2653_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2648_, v_x_2649_, v___x_2652_, v_x_2650_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2654_, lean_object* v_x_2655_, lean_object* v_x_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2654_, v_x_2655_, v_x_2656_);
lean_dec_ref(v_x_2655_);
lean_dec_ref(v___x_2654_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2658_, lean_object* v_x_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_){
_start:
{
lean_object* v_ks_2663_; lean_object* v_vs_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2688_; 
v_ks_2663_ = lean_ctor_get(v_x_2659_, 0);
v_vs_2664_ = lean_ctor_get(v_x_2659_, 1);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_x_2659_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2666_ = v_x_2659_;
v_isShared_2667_ = v_isSharedCheck_2688_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_vs_2664_);
lean_inc(v_ks_2663_);
lean_dec(v_x_2659_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2688_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = lean_array_get_size(v_ks_2663_);
v___x_2669_ = lean_nat_dec_lt(v_x_2660_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
lean_dec(v_x_2660_);
v___x_2670_ = lean_array_push(v_ks_2663_, v_x_2661_);
v___x_2671_ = lean_array_push(v_vs_2664_, v_x_2662_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2671_);
lean_ctor_set(v___x_2666_, 0, v___x_2670_);
v___x_2673_ = v___x_2666_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
else
{
lean_object* v_k_x27_2675_; uint8_t v___x_2676_; 
v_k_x27_2675_ = lean_array_fget_borrowed(v_ks_2663_, v_x_2660_);
lean_inc(v_k_x27_2675_);
lean_inc_ref(v_x_2661_);
v___x_2676_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2658_, v_x_2661_, v_k_x27_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2678_; 
if (v_isShared_2667_ == 0)
{
v___x_2678_ = v___x_2666_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_ks_2663_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_vs_2664_);
v___x_2678_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = lean_unsigned_to_nat(1u);
v___x_2680_ = lean_nat_add(v_x_2660_, v___x_2679_);
lean_dec(v_x_2660_);
v_x_2659_ = v___x_2678_;
v_x_2660_ = v___x_2680_;
goto _start;
}
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
v___x_2683_ = lean_array_fset(v_ks_2663_, v_x_2660_, v_x_2661_);
v___x_2684_ = lean_array_fset(v_vs_2664_, v_x_2660_, v_x_2662_);
lean_dec(v_x_2660_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2684_);
lean_ctor_set(v___x_2666_, 0, v___x_2683_);
v___x_2686_ = v___x_2666_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2689_, lean_object* v_x_2690_, lean_object* v_x_2691_, lean_object* v_x_2692_, lean_object* v_x_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2689_, v_x_2690_, v_x_2691_, v_x_2692_, v_x_2693_);
lean_dec_ref(v___x_2689_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2695_, lean_object* v_n_2696_, lean_object* v_k_2697_, lean_object* v_v_2698_){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_unsigned_to_nat(0u);
v___x_2700_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2695_, v_n_2696_, v___x_2699_, v_k_2697_, v_v_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2701_, lean_object* v_n_2702_, lean_object* v_k_2703_, lean_object* v_v_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2701_, v_n_2702_, v_k_2703_, v_v_2704_);
lean_dec_ref(v___x_2701_);
return v_res_2705_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2707_, lean_object* v_x_2708_, size_t v_x_2709_, size_t v_x_2710_, lean_object* v_x_2711_, lean_object* v_x_2712_){
_start:
{
if (lean_obj_tag(v_x_2708_) == 0)
{
lean_object* v_es_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; lean_object* v_j_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v_es_2713_ = lean_ctor_get(v_x_2708_, 0);
v___x_2714_ = ((size_t)5ULL);
v___x_2715_ = ((size_t)1ULL);
v___x_2716_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2717_ = lean_usize_land(v_x_2709_, v___x_2716_);
v_j_2718_ = lean_usize_to_nat(v___x_2717_);
v___x_2719_ = lean_array_get_size(v_es_2713_);
v___x_2720_ = lean_nat_dec_lt(v_j_2718_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_dec(v_j_2718_);
lean_dec(v_x_2712_);
lean_dec_ref(v_x_2711_);
return v_x_2708_;
}
else
{
lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2757_; 
lean_inc_ref(v_es_2713_);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_x_2708_);
if (v_isSharedCheck_2757_ == 0)
{
lean_object* v_unused_2758_; 
v_unused_2758_ = lean_ctor_get(v_x_2708_, 0);
lean_dec(v_unused_2758_);
v___x_2722_ = v_x_2708_;
v_isShared_2723_ = v_isSharedCheck_2757_;
goto v_resetjp_2721_;
}
else
{
lean_dec(v_x_2708_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2757_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v_v_2724_; lean_object* v___x_2725_; lean_object* v_xs_x27_2726_; lean_object* v___y_2728_; 
v_v_2724_ = lean_array_fget(v_es_2713_, v_j_2718_);
v___x_2725_ = lean_box(0);
v_xs_x27_2726_ = lean_array_fset(v_es_2713_, v_j_2718_, v___x_2725_);
switch(lean_obj_tag(v_v_2724_))
{
case 0:
{
lean_object* v_key_2733_; lean_object* v_val_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2744_; 
v_key_2733_ = lean_ctor_get(v_v_2724_, 0);
v_val_2734_ = lean_ctor_get(v_v_2724_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_v_2724_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2736_ = v_v_2724_;
v_isShared_2737_ = v_isSharedCheck_2744_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_val_2734_);
lean_inc(v_key_2733_);
lean_dec(v_v_2724_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2744_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
uint8_t v___x_2738_; 
lean_inc(v_key_2733_);
lean_inc_ref(v_x_2711_);
v___x_2738_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2707_, v_x_2711_, v_key_2733_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_del_object(v___x_2736_);
v___x_2739_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2733_, v_val_2734_, v_x_2711_, v_x_2712_);
v___x_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
v___y_2728_ = v___x_2740_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2742_; 
lean_dec(v_val_2734_);
lean_dec(v_key_2733_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v_x_2712_);
lean_ctor_set(v___x_2736_, 0, v_x_2711_);
v___x_2742_ = v___x_2736_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_x_2711_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_x_2712_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
v___y_2728_ = v___x_2742_;
goto v___jp_2727_;
}
}
}
}
case 1:
{
lean_object* v_node_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2755_; 
v_node_2745_ = lean_ctor_get(v_v_2724_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_v_2724_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2747_ = v_v_2724_;
v_isShared_2748_ = v_isSharedCheck_2755_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_node_2745_);
lean_dec(v_v_2724_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2755_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
size_t v___x_2749_; size_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2749_ = lean_usize_shift_right(v_x_2709_, v___x_2714_);
v___x_2750_ = lean_usize_add(v_x_2710_, v___x_2715_);
v___x_2751_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2707_, v_node_2745_, v___x_2749_, v___x_2750_, v_x_2711_, v_x_2712_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2751_);
v___x_2753_ = v___x_2747_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
v___y_2728_ = v___x_2753_;
goto v___jp_2727_;
}
}
}
default: 
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v_x_2711_);
lean_ctor_set(v___x_2756_, 1, v_x_2712_);
v___y_2728_ = v___x_2756_;
goto v___jp_2727_;
}
}
v___jp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2729_ = lean_array_fset(v_xs_x27_2726_, v_j_2718_, v___y_2728_);
lean_dec(v_j_2718_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2729_);
v___x_2731_ = v___x_2722_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
else
{
lean_object* v_ks_2759_; lean_object* v_vs_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2780_; 
v_ks_2759_ = lean_ctor_get(v_x_2708_, 0);
v_vs_2760_ = lean_ctor_get(v_x_2708_, 1);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_x_2708_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2762_ = v_x_2708_;
v_isShared_2763_ = v_isSharedCheck_2780_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_vs_2760_);
lean_inc(v_ks_2759_);
lean_dec(v_x_2708_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2780_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_ks_2759_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_vs_2760_);
v___x_2765_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v_newNode_2766_; uint8_t v___y_2768_; size_t v___x_2774_; uint8_t v___x_2775_; 
v_newNode_2766_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2707_, v___x_2765_, v_x_2711_, v_x_2712_);
v___x_2774_ = ((size_t)7ULL);
v___x_2775_ = lean_usize_dec_le(v___x_2774_, v_x_2710_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2776_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2766_);
v___x_2777_ = lean_unsigned_to_nat(4u);
v___x_2778_ = lean_nat_dec_lt(v___x_2776_, v___x_2777_);
lean_dec(v___x_2776_);
v___y_2768_ = v___x_2778_;
goto v___jp_2767_;
}
else
{
v___y_2768_ = v___x_2775_;
goto v___jp_2767_;
}
v___jp_2767_:
{
if (v___y_2768_ == 0)
{
lean_object* v_ks_2769_; lean_object* v_vs_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_ks_2769_ = lean_ctor_get(v_newNode_2766_, 0);
lean_inc_ref(v_ks_2769_);
v_vs_2770_ = lean_ctor_get(v_newNode_2766_, 1);
lean_inc_ref(v_vs_2770_);
lean_dec_ref(v_newNode_2766_);
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2707_, v_x_2710_, v_ks_2769_, v_vs_2770_, v___x_2771_, v___x_2772_);
lean_dec_ref(v_vs_2770_);
lean_dec_ref(v_ks_2769_);
return v___x_2773_;
}
else
{
return v_newNode_2766_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2781_, size_t v_depth_2782_, lean_object* v_keys_2783_, lean_object* v_vals_2784_, lean_object* v_i_2785_, lean_object* v_entries_2786_){
_start:
{
lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2787_ = lean_array_get_size(v_keys_2783_);
v___x_2788_ = lean_nat_dec_lt(v_i_2785_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_dec(v_i_2785_);
return v_entries_2786_;
}
else
{
lean_object* v_k_2789_; lean_object* v_v_2790_; uint64_t v___x_2791_; size_t v_h_2792_; size_t v___x_2793_; lean_object* v___x_2794_; size_t v___x_2795_; size_t v___x_2796_; size_t v___x_2797_; size_t v_h_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_k_2789_ = lean_array_fget_borrowed(v_keys_2783_, v_i_2785_);
v_v_2790_ = lean_array_fget_borrowed(v_vals_2784_, v_i_2785_);
lean_inc_n(v_k_2789_, 2);
v___x_2791_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2781_, v_k_2789_);
v_h_2792_ = lean_uint64_to_usize(v___x_2791_);
v___x_2793_ = ((size_t)5ULL);
v___x_2794_ = lean_unsigned_to_nat(1u);
v___x_2795_ = ((size_t)1ULL);
v___x_2796_ = lean_usize_sub(v_depth_2782_, v___x_2795_);
v___x_2797_ = lean_usize_mul(v___x_2793_, v___x_2796_);
v_h_2798_ = lean_usize_shift_right(v_h_2792_, v___x_2797_);
v___x_2799_ = lean_nat_add(v_i_2785_, v___x_2794_);
lean_dec(v_i_2785_);
lean_inc(v_v_2790_);
v___x_2800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2781_, v_entries_2786_, v_h_2798_, v_depth_2782_, v_k_2789_, v_v_2790_);
v_i_2785_ = v___x_2799_;
v_entries_2786_ = v___x_2800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2802_, lean_object* v_depth_2803_, lean_object* v_keys_2804_, lean_object* v_vals_2805_, lean_object* v_i_2806_, lean_object* v_entries_2807_){
_start:
{
size_t v_depth_boxed_2808_; lean_object* v_res_2809_; 
v_depth_boxed_2808_ = lean_unbox_usize(v_depth_2803_);
lean_dec(v_depth_2803_);
v_res_2809_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2802_, v_depth_boxed_2808_, v_keys_2804_, v_vals_2805_, v_i_2806_, v_entries_2807_);
lean_dec_ref(v_vals_2805_);
lean_dec_ref(v_keys_2804_);
lean_dec_ref(v___x_2802_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_){
_start:
{
size_t v_x_27805__boxed_2816_; size_t v_x_27806__boxed_2817_; lean_object* v_res_2818_; 
v_x_27805__boxed_2816_ = lean_unbox_usize(v_x_2812_);
lean_dec(v_x_2812_);
v_x_27806__boxed_2817_ = lean_unbox_usize(v_x_2813_);
lean_dec(v_x_2813_);
v_res_2818_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2810_, v_x_2811_, v_x_27805__boxed_2816_, v_x_27806__boxed_2817_, v_x_2814_, v_x_2815_);
lean_dec_ref(v___x_2810_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2819_, lean_object* v_x_2820_, lean_object* v_x_2821_, lean_object* v_x_2822_){
_start:
{
uint64_t v___x_2823_; size_t v___x_2824_; size_t v___x_2825_; lean_object* v___x_2826_; 
lean_inc_ref(v_x_2821_);
v___x_2823_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2819_, v_x_2821_);
v___x_2824_ = lean_uint64_to_usize(v___x_2823_);
v___x_2825_ = ((size_t)1ULL);
v___x_2826_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2819_, v_x_2820_, v___x_2824_, v___x_2825_, v_x_2821_, v_x_2822_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2827_, lean_object* v_x_2828_, lean_object* v_x_2829_, lean_object* v_x_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2827_, v_x_2828_, v_x_2829_, v_x_2830_);
lean_dec_ref(v___x_2827_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2836_, lean_object* v_rootNew_2837_, uint8_t v_a_2838_, lean_object* v_b_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v___x_2847_; lean_object* v_snd_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_3015_; 
v___x_2847_ = lean_st_ref_get(v___y_2840_);
v_snd_2848_ = lean_ctor_get(v_b_2839_, 1);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_b_2839_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v_b_2839_, 0);
lean_dec(v_unused_3016_);
v___x_2850_ = v_b_2839_;
v_isShared_2851_ = v_isSharedCheck_3015_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_snd_2848_);
lean_dec(v_b_2839_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_3015_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; 
lean_inc(v_snd_2848_);
v___x_2852_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2847_, v_snd_2848_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___x_2847_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_3006_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_3006_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_3006_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_self_2857_; lean_object* v_next_2858_; lean_object* v_congr_2859_; lean_object* v_target_x3f_2860_; lean_object* v_proof_x3f_2861_; uint8_t v_flipped_2862_; lean_object* v_size_2863_; uint8_t v_interpreted_2864_; uint8_t v_ctor_2865_; uint8_t v_hasLambdas_2866_; uint8_t v_heqProofs_2867_; lean_object* v_idx_2868_; lean_object* v_generation_2869_; lean_object* v_mt_2870_; lean_object* v_sTerms_2871_; uint8_t v_funCC_2872_; lean_object* v_ematchDiagSource_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_3004_; 
v_self_2857_ = lean_ctor_get(v_a_2853_, 0);
v_next_2858_ = lean_ctor_get(v_a_2853_, 1);
v_congr_2859_ = lean_ctor_get(v_a_2853_, 3);
v_target_x3f_2860_ = lean_ctor_get(v_a_2853_, 4);
v_proof_x3f_2861_ = lean_ctor_get(v_a_2853_, 5);
v_flipped_2862_ = lean_ctor_get_uint8(v_a_2853_, sizeof(void*)*12);
v_size_2863_ = lean_ctor_get(v_a_2853_, 6);
v_interpreted_2864_ = lean_ctor_get_uint8(v_a_2853_, sizeof(void*)*12 + 1);
v_ctor_2865_ = lean_ctor_get_uint8(v_a_2853_, sizeof(void*)*12 + 2);
v_hasLambdas_2866_ = lean_ctor_get_uint8(v_a_2853_, sizeof(void*)*12 + 3);
v_heqProofs_2867_ = lean_ctor_get_uint8(v_a_2853_, sizeof(void*)*12 + 4);
v_idx_2868_ = lean_ctor_get(v_a_2853_, 7);
v_generation_2869_ = lean_ctor_get(v_a_2853_, 8);
v_mt_2870_ = lean_ctor_get(v_a_2853_, 9);
v_sTerms_2871_ = lean_ctor_get(v_a_2853_, 10);
v_funCC_2872_ = lean_ctor_get_uint8(v_a_2853_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2873_ = lean_ctor_get(v_a_2853_, 11);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_a_2853_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; 
v_unused_3005_ = lean_ctor_get(v_a_2853_, 2);
lean_dec(v_unused_3005_);
v___x_2875_ = v_a_2853_;
v_isShared_2876_ = v_isSharedCheck_3004_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_ematchDiagSource_2873_);
lean_inc(v_sTerms_2871_);
lean_inc(v_mt_2870_);
lean_inc(v_generation_2869_);
lean_inc(v_idx_2868_);
lean_inc(v_size_2863_);
lean_inc(v_proof_x3f_2861_);
lean_inc(v_target_x3f_2860_);
lean_inc(v_congr_2859_);
lean_inc(v_next_2858_);
lean_inc(v_self_2857_);
lean_dec(v_a_2853_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_3004_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v___y_2892_; lean_object* v___x_2902_; 
v___x_2877_ = lean_box(0);
lean_inc(v_ematchDiagSource_2873_);
lean_inc(v_sTerms_2871_);
lean_inc(v_mt_2870_);
lean_inc(v_generation_2869_);
lean_inc(v_idx_2868_);
lean_inc(v_size_2863_);
lean_inc(v_proof_x3f_2861_);
lean_inc(v_target_x3f_2860_);
lean_inc_ref(v_rootNew_2837_);
lean_inc_ref(v_next_2858_);
lean_inc_ref(v_self_2857_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 2, v_rootNew_2837_);
v___x_2902_ = v___x_2875_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_self_2857_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_next_2858_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v_rootNew_2837_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v_congr_2859_);
lean_ctor_set(v_reuseFailAlloc_3003_, 4, v_target_x3f_2860_);
lean_ctor_set(v_reuseFailAlloc_3003_, 5, v_proof_x3f_2861_);
lean_ctor_set(v_reuseFailAlloc_3003_, 6, v_size_2863_);
lean_ctor_set(v_reuseFailAlloc_3003_, 7, v_idx_2868_);
lean_ctor_set(v_reuseFailAlloc_3003_, 8, v_generation_2869_);
lean_ctor_set(v_reuseFailAlloc_3003_, 9, v_mt_2870_);
lean_ctor_set(v_reuseFailAlloc_3003_, 10, v_sTerms_2871_);
lean_ctor_set(v_reuseFailAlloc_3003_, 11, v_ematchDiagSource_2873_);
lean_ctor_set_uint8(v_reuseFailAlloc_3003_, sizeof(void*)*12, v_flipped_2862_);
lean_ctor_set_uint8(v_reuseFailAlloc_3003_, sizeof(void*)*12 + 1, v_interpreted_2864_);
lean_ctor_set_uint8(v_reuseFailAlloc_3003_, sizeof(void*)*12 + 2, v_ctor_2865_);
lean_ctor_set_uint8(v_reuseFailAlloc_3003_, sizeof(void*)*12 + 3, v_hasLambdas_2866_);
lean_ctor_set_uint8(v_reuseFailAlloc_3003_, sizeof(void*)*12 + 4, v_heqProofs_2867_);
lean_ctor_set_uint8(v_reuseFailAlloc_3003_, sizeof(void*)*12 + 5, v_funCC_2872_);
v___x_2902_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2901_;
}
v___jp_2878_:
{
uint8_t v___x_2879_; 
v___x_2879_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_2858_, v_lhs_2836_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2881_; 
lean_del_object(v___x_2855_);
lean_dec(v_snd_2848_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 1, v_next_2858_);
lean_ctor_set(v___x_2850_, 0, v___x_2877_);
v___x_2881_ = v___x_2850_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_next_2858_);
v___x_2881_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
v_b_2839_ = v___x_2881_;
goto _start;
}
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2886_; 
lean_dec_ref(v_next_2858_);
lean_dec_ref(v_rootNew_2837_);
v___x_2884_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2884_);
v___x_2886_ = v___x_2850_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2884_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_snd_2848_);
v___x_2886_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2886_);
v___x_2888_ = v___x_2855_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
v___jp_2891_:
{
if (lean_obj_tag(v___y_2892_) == 0)
{
lean_dec_ref(v___y_2892_);
goto v___jp_2878_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec_ref(v_next_2858_);
lean_del_object(v___x_2855_);
lean_del_object(v___x_2850_);
lean_dec(v_snd_2848_);
lean_dec_ref(v_rootNew_2837_);
v_a_2893_ = lean_ctor_get(v___y_2892_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___y_2892_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___y_2892_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___y_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; 
lean_inc_ref(v___x_2902_);
lean_inc_ref(v_self_2857_);
v___x_2903_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2857_, v___x_2902_, v___y_2840_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_dec_ref(v___x_2903_);
if (v_a_2838_ == 0)
{
lean_dec_ref(v___x_2902_);
lean_dec(v_ematchDiagSource_2873_);
lean_dec(v_sTerms_2871_);
lean_dec(v_mt_2870_);
lean_dec(v_generation_2869_);
lean_dec(v_idx_2868_);
lean_dec(v_size_2863_);
lean_dec(v_proof_x3f_2861_);
lean_dec(v_target_x3f_2860_);
lean_dec_ref(v_self_2857_);
goto v___jp_2878_;
}
else
{
lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2904_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2905_ = lean_unsigned_to_nat(3u);
v___x_2906_ = l_Lean_Expr_isAppOfArity(v_self_2857_, v___x_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_dec_ref(v___x_2902_);
lean_dec(v_ematchDiagSource_2873_);
lean_dec(v_sTerms_2871_);
lean_dec(v_mt_2870_);
lean_dec(v_generation_2869_);
lean_dec(v_idx_2868_);
lean_dec(v_size_2863_);
lean_dec(v_proof_x3f_2861_);
lean_dec(v_target_x3f_2860_);
lean_dec_ref(v_self_2857_);
goto v___jp_2878_;
}
else
{
uint8_t v___x_2907_; 
v___x_2907_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2902_);
lean_dec_ref(v___x_2902_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v_toGoalState_2909_; lean_object* v_enodeMap_2910_; lean_object* v_congrTable_2911_; lean_object* v___x_2912_; 
v___x_2908_ = lean_st_ref_get(v___y_2840_);
v_toGoalState_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc_ref(v_toGoalState_2909_);
lean_dec(v___x_2908_);
v_enodeMap_2910_ = lean_ctor_get(v_toGoalState_2909_, 1);
lean_inc_ref(v_enodeMap_2910_);
v_congrTable_2911_ = lean_ctor_get(v_toGoalState_2909_, 4);
lean_inc_ref(v_congrTable_2911_);
lean_dec_ref(v_toGoalState_2909_);
lean_inc_ref(v_self_2857_);
v___x_2912_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_2910_, v_congrTable_2911_, v_self_2857_);
lean_dec_ref(v_congrTable_2911_);
lean_dec_ref(v_enodeMap_2910_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_dec(v_ematchDiagSource_2873_);
lean_dec(v_sTerms_2871_);
lean_dec(v_mt_2870_);
lean_dec(v_generation_2869_);
lean_dec(v_idx_2868_);
lean_dec(v_size_2863_);
lean_dec(v_proof_x3f_2861_);
lean_dec(v_target_x3f_2860_);
lean_dec_ref(v_self_2857_);
goto v___jp_2878_;
}
else
{
lean_object* v_val_2913_; lean_object* v_fst_2914_; lean_object* v___x_2915_; 
v_val_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_val_2913_);
lean_dec_ref(v___x_2912_);
v_fst_2914_ = lean_ctor_get(v_val_2913_, 0);
lean_inc(v_fst_2914_);
lean_dec(v_val_2913_);
v___x_2915_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_2914_, v___y_2841_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; uint8_t v___x_2917_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref(v___x_2915_);
v___x_2917_ = lean_unbox(v_a_2916_);
lean_dec(v_a_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v_toGoalState_2919_; lean_object* v_mvarId_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2994_; 
v___x_2918_ = lean_st_ref_take(v___y_2840_);
v_toGoalState_2919_ = lean_ctor_get(v___x_2918_, 0);
v_mvarId_2920_ = lean_ctor_get(v___x_2918_, 1);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2922_ = v___x_2918_;
v_isShared_2923_ = v_isSharedCheck_2994_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_mvarId_2920_);
lean_inc(v_toGoalState_2919_);
lean_dec(v___x_2918_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2994_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v_nextDeclIdx_2924_; lean_object* v_enodeMap_2925_; lean_object* v_exprs_2926_; lean_object* v_parents_2927_; lean_object* v_congrTable_2928_; lean_object* v_appMap_2929_; lean_object* v_indicesFound_2930_; lean_object* v_newFacts_2931_; uint8_t v_inconsistent_2932_; lean_object* v_nextIdx_2933_; lean_object* v_newRawFacts_2934_; lean_object* v_facts_2935_; lean_object* v_extThms_2936_; lean_object* v_ematch_2937_; lean_object* v_inj_2938_; lean_object* v_split_2939_; lean_object* v_clean_2940_; lean_object* v_sstates_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2993_; 
v_nextDeclIdx_2924_ = lean_ctor_get(v_toGoalState_2919_, 0);
v_enodeMap_2925_ = lean_ctor_get(v_toGoalState_2919_, 1);
v_exprs_2926_ = lean_ctor_get(v_toGoalState_2919_, 2);
v_parents_2927_ = lean_ctor_get(v_toGoalState_2919_, 3);
v_congrTable_2928_ = lean_ctor_get(v_toGoalState_2919_, 4);
v_appMap_2929_ = lean_ctor_get(v_toGoalState_2919_, 5);
v_indicesFound_2930_ = lean_ctor_get(v_toGoalState_2919_, 6);
v_newFacts_2931_ = lean_ctor_get(v_toGoalState_2919_, 7);
v_inconsistent_2932_ = lean_ctor_get_uint8(v_toGoalState_2919_, sizeof(void*)*17);
v_nextIdx_2933_ = lean_ctor_get(v_toGoalState_2919_, 8);
v_newRawFacts_2934_ = lean_ctor_get(v_toGoalState_2919_, 9);
v_facts_2935_ = lean_ctor_get(v_toGoalState_2919_, 10);
v_extThms_2936_ = lean_ctor_get(v_toGoalState_2919_, 11);
v_ematch_2937_ = lean_ctor_get(v_toGoalState_2919_, 12);
v_inj_2938_ = lean_ctor_get(v_toGoalState_2919_, 13);
v_split_2939_ = lean_ctor_get(v_toGoalState_2919_, 14);
v_clean_2940_ = lean_ctor_get(v_toGoalState_2919_, 15);
v_sstates_2941_ = lean_ctor_get(v_toGoalState_2919_, 16);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_toGoalState_2919_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2943_ = v_toGoalState_2919_;
v_isShared_2944_ = v_isSharedCheck_2993_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_sstates_2941_);
lean_inc(v_clean_2940_);
lean_inc(v_split_2939_);
lean_inc(v_inj_2938_);
lean_inc(v_ematch_2937_);
lean_inc(v_extThms_2936_);
lean_inc(v_facts_2935_);
lean_inc(v_newRawFacts_2934_);
lean_inc(v_nextIdx_2933_);
lean_inc(v_newFacts_2931_);
lean_inc(v_indicesFound_2930_);
lean_inc(v_appMap_2929_);
lean_inc(v_congrTable_2928_);
lean_inc(v_parents_2927_);
lean_inc(v_exprs_2926_);
lean_inc(v_enodeMap_2925_);
lean_inc(v_nextDeclIdx_2924_);
lean_dec(v_toGoalState_2919_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2993_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2945_ = lean_box(0);
lean_inc_ref(v_self_2857_);
v___x_2946_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_2925_, v_congrTable_2928_, v_self_2857_, v___x_2945_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 4, v___x_2946_);
v___x_2948_ = v___x_2943_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_nextDeclIdx_2924_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_enodeMap_2925_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_exprs_2926_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v_parents_2927_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2992_, 5, v_appMap_2929_);
lean_ctor_set(v_reuseFailAlloc_2992_, 6, v_indicesFound_2930_);
lean_ctor_set(v_reuseFailAlloc_2992_, 7, v_newFacts_2931_);
lean_ctor_set(v_reuseFailAlloc_2992_, 8, v_nextIdx_2933_);
lean_ctor_set(v_reuseFailAlloc_2992_, 9, v_newRawFacts_2934_);
lean_ctor_set(v_reuseFailAlloc_2992_, 10, v_facts_2935_);
lean_ctor_set(v_reuseFailAlloc_2992_, 11, v_extThms_2936_);
lean_ctor_set(v_reuseFailAlloc_2992_, 12, v_ematch_2937_);
lean_ctor_set(v_reuseFailAlloc_2992_, 13, v_inj_2938_);
lean_ctor_set(v_reuseFailAlloc_2992_, 14, v_split_2939_);
lean_ctor_set(v_reuseFailAlloc_2992_, 15, v_clean_2940_);
lean_ctor_set(v_reuseFailAlloc_2992_, 16, v_sstates_2941_);
lean_ctor_set_uint8(v_reuseFailAlloc_2992_, sizeof(void*)*17, v_inconsistent_2932_);
v___x_2948_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2950_; 
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v___x_2948_);
v___x_2950_ = v___x_2922_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_mvarId_2920_);
v___x_2950_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_st_ref_set(v___y_2840_, v___x_2950_);
lean_inc_ref(v_rootNew_2837_);
lean_inc_ref(v_next_2858_);
lean_inc_ref_n(v_self_2857_, 3);
v___x_2952_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_2952_, 0, v_self_2857_);
lean_ctor_set(v___x_2952_, 1, v_next_2858_);
lean_ctor_set(v___x_2952_, 2, v_rootNew_2837_);
lean_ctor_set(v___x_2952_, 3, v_self_2857_);
lean_ctor_set(v___x_2952_, 4, v_target_x3f_2860_);
lean_ctor_set(v___x_2952_, 5, v_proof_x3f_2861_);
lean_ctor_set(v___x_2952_, 6, v_size_2863_);
lean_ctor_set(v___x_2952_, 7, v_idx_2868_);
lean_ctor_set(v___x_2952_, 8, v_generation_2869_);
lean_ctor_set(v___x_2952_, 9, v_mt_2870_);
lean_ctor_set(v___x_2952_, 10, v_sTerms_2871_);
lean_ctor_set(v___x_2952_, 11, v_ematchDiagSource_2873_);
lean_ctor_set_uint8(v___x_2952_, sizeof(void*)*12, v_flipped_2862_);
lean_ctor_set_uint8(v___x_2952_, sizeof(void*)*12 + 1, v_interpreted_2864_);
lean_ctor_set_uint8(v___x_2952_, sizeof(void*)*12 + 2, v_ctor_2865_);
lean_ctor_set_uint8(v___x_2952_, sizeof(void*)*12 + 3, v_hasLambdas_2866_);
lean_ctor_set_uint8(v___x_2952_, sizeof(void*)*12 + 4, v_heqProofs_2867_);
lean_ctor_set_uint8(v___x_2952_, sizeof(void*)*12 + 5, v_funCC_2872_);
v___x_2953_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2857_, v___x_2952_, v___y_2840_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_dec_ref(v___x_2953_);
v___x_2954_ = lean_st_ref_get(v___y_2840_);
lean_inc(v_fst_2914_);
v___x_2955_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2954_, v_fst_2914_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___x_2954_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v_self_2957_; lean_object* v_next_2958_; lean_object* v_root_2959_; lean_object* v_target_x3f_2960_; lean_object* v_proof_x3f_2961_; uint8_t v_flipped_2962_; lean_object* v_size_2963_; uint8_t v_interpreted_2964_; uint8_t v_ctor_2965_; uint8_t v_hasLambdas_2966_; uint8_t v_heqProofs_2967_; lean_object* v_idx_2968_; lean_object* v_generation_2969_; lean_object* v_mt_2970_; lean_object* v_sTerms_2971_; uint8_t v_funCC_2972_; lean_object* v_ematchDiagSource_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2981_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref(v___x_2955_);
v_self_2957_ = lean_ctor_get(v_a_2956_, 0);
v_next_2958_ = lean_ctor_get(v_a_2956_, 1);
v_root_2959_ = lean_ctor_get(v_a_2956_, 2);
v_target_x3f_2960_ = lean_ctor_get(v_a_2956_, 4);
v_proof_x3f_2961_ = lean_ctor_get(v_a_2956_, 5);
v_flipped_2962_ = lean_ctor_get_uint8(v_a_2956_, sizeof(void*)*12);
v_size_2963_ = lean_ctor_get(v_a_2956_, 6);
v_interpreted_2964_ = lean_ctor_get_uint8(v_a_2956_, sizeof(void*)*12 + 1);
v_ctor_2965_ = lean_ctor_get_uint8(v_a_2956_, sizeof(void*)*12 + 2);
v_hasLambdas_2966_ = lean_ctor_get_uint8(v_a_2956_, sizeof(void*)*12 + 3);
v_heqProofs_2967_ = lean_ctor_get_uint8(v_a_2956_, sizeof(void*)*12 + 4);
v_idx_2968_ = lean_ctor_get(v_a_2956_, 7);
v_generation_2969_ = lean_ctor_get(v_a_2956_, 8);
v_mt_2970_ = lean_ctor_get(v_a_2956_, 9);
v_sTerms_2971_ = lean_ctor_get(v_a_2956_, 10);
v_funCC_2972_ = lean_ctor_get_uint8(v_a_2956_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2973_ = lean_ctor_get(v_a_2956_, 11);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_a_2956_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v_a_2956_, 3);
lean_dec(v_unused_2982_);
v___x_2975_ = v_a_2956_;
v_isShared_2976_ = v_isSharedCheck_2981_;
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
lean_inc(v_root_2959_);
lean_inc(v_next_2958_);
lean_inc(v_self_2957_);
lean_dec(v_a_2956_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2981_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 3, v_self_2857_);
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_self_2957_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_next_2958_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_root_2959_);
lean_ctor_set(v_reuseFailAlloc_2980_, 3, v_self_2857_);
lean_ctor_set(v_reuseFailAlloc_2980_, 4, v_target_x3f_2960_);
lean_ctor_set(v_reuseFailAlloc_2980_, 5, v_proof_x3f_2961_);
lean_ctor_set(v_reuseFailAlloc_2980_, 6, v_size_2963_);
lean_ctor_set(v_reuseFailAlloc_2980_, 7, v_idx_2968_);
lean_ctor_set(v_reuseFailAlloc_2980_, 8, v_generation_2969_);
lean_ctor_set(v_reuseFailAlloc_2980_, 9, v_mt_2970_);
lean_ctor_set(v_reuseFailAlloc_2980_, 10, v_sTerms_2971_);
lean_ctor_set(v_reuseFailAlloc_2980_, 11, v_ematchDiagSource_2973_);
lean_ctor_set_uint8(v_reuseFailAlloc_2980_, sizeof(void*)*12, v_flipped_2962_);
lean_ctor_set_uint8(v_reuseFailAlloc_2980_, sizeof(void*)*12 + 1, v_interpreted_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_2980_, sizeof(void*)*12 + 2, v_ctor_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_2980_, sizeof(void*)*12 + 3, v_hasLambdas_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_2980_, sizeof(void*)*12 + 4, v_heqProofs_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_2980_, sizeof(void*)*12 + 5, v_funCC_2972_);
v___x_2978_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_2914_, v___x_2978_, v___y_2840_);
v___y_2892_ = v___x_2979_;
goto v___jp_2891_;
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v_fst_2914_);
lean_dec_ref(v_next_2858_);
lean_dec_ref(v_self_2857_);
lean_del_object(v___x_2855_);
lean_del_object(v___x_2850_);
lean_dec(v_snd_2848_);
lean_dec_ref(v_rootNew_2837_);
v_a_2983_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2955_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2955_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_dec(v_fst_2914_);
lean_dec_ref(v_self_2857_);
v___y_2892_ = v___x_2953_;
goto v___jp_2891_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2914_);
lean_dec(v_ematchDiagSource_2873_);
lean_dec(v_sTerms_2871_);
lean_dec(v_mt_2870_);
lean_dec(v_generation_2869_);
lean_dec(v_idx_2868_);
lean_dec(v_size_2863_);
lean_dec(v_proof_x3f_2861_);
lean_dec(v_target_x3f_2860_);
lean_dec_ref(v_self_2857_);
goto v___jp_2878_;
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v_fst_2914_);
lean_dec(v_ematchDiagSource_2873_);
lean_dec(v_sTerms_2871_);
lean_dec(v_mt_2870_);
lean_dec(v_generation_2869_);
lean_dec(v_idx_2868_);
lean_dec(v_size_2863_);
lean_dec(v_proof_x3f_2861_);
lean_dec(v_target_x3f_2860_);
lean_dec_ref(v_next_2858_);
lean_dec_ref(v_self_2857_);
lean_del_object(v___x_2855_);
lean_del_object(v___x_2850_);
lean_dec(v_snd_2848_);
lean_dec_ref(v_rootNew_2837_);
v_a_2995_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2915_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2915_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2873_);
lean_dec(v_sTerms_2871_);
lean_dec(v_mt_2870_);
lean_dec(v_generation_2869_);
lean_dec(v_idx_2868_);
lean_dec(v_size_2863_);
lean_dec(v_proof_x3f_2861_);
lean_dec(v_target_x3f_2860_);
lean_dec_ref(v_self_2857_);
goto v___jp_2878_;
}
}
}
}
else
{
lean_dec_ref(v___x_2902_);
lean_dec(v_ematchDiagSource_2873_);
lean_dec(v_sTerms_2871_);
lean_dec(v_mt_2870_);
lean_dec(v_generation_2869_);
lean_dec(v_idx_2868_);
lean_dec(v_size_2863_);
lean_dec(v_proof_x3f_2861_);
lean_dec(v_target_x3f_2860_);
lean_dec_ref(v_self_2857_);
v___y_2892_ = v___x_2903_;
goto v___jp_2891_;
}
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_del_object(v___x_2850_);
lean_dec(v_snd_2848_);
lean_dec_ref(v_rootNew_2837_);
v_a_3007_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2852_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2852_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3017_, lean_object* v_rootNew_3018_, lean_object* v_a_3019_, lean_object* v_b_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
uint8_t v_a_27993__boxed_3028_; lean_object* v_res_3029_; 
v_a_27993__boxed_3028_ = lean_unbox(v_a_3019_);
v_res_3029_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3017_, v_rootNew_3018_, v_a_27993__boxed_3028_, v_b_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v_lhs_3017_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3030_, lean_object* v_rootNew_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3031_, v_a_3036_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref(v___x_3043_);
v___x_3045_ = lean_box(0);
lean_inc_ref(v_lhs_3030_);
v___x_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set(v___x_3046_, 1, v_lhs_3030_);
v___x_3047_ = lean_unbox(v_a_3044_);
lean_dec(v_a_3044_);
v___x_3048_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3030_, v_rootNew_3031_, v___x_3047_, v___x_3046_, v_a_3032_, v_a_3036_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_);
lean_dec_ref(v_lhs_3030_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3062_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3062_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3062_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v_fst_3053_; 
v_fst_3053_ = lean_ctor_get(v_a_3049_, 0);
lean_inc(v_fst_3053_);
lean_dec(v_a_3049_);
if (lean_obj_tag(v_fst_3053_) == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3054_ = lean_box(0);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3054_);
v___x_3056_ = v___x_3051_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
else
{
lean_object* v_val_3058_; lean_object* v___x_3060_; 
v_val_3058_ = lean_ctor_get(v_fst_3053_, 0);
lean_inc(v_val_3058_);
lean_dec_ref(v_fst_3053_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v_val_3058_);
v___x_3060_ = v___x_3051_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_val_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
v_a_3063_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3048_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3048_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v_rootNew_3031_);
lean_dec_ref(v_lhs_3030_);
v_a_3071_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3043_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3043_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3079_, lean_object* v_rootNew_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3079_, v_rootNew_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec(v_a_3081_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3093_, lean_object* v_00_u03b2_3094_, lean_object* v_x_3095_, lean_object* v_x_3096_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3093_, v_x_3095_, v_x_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3098_, lean_object* v_00_u03b2_3099_, lean_object* v_x_3100_, lean_object* v_x_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3098_, v_00_u03b2_3099_, v_x_3100_, v_x_3101_);
lean_dec_ref(v_x_3100_);
lean_dec_ref(v___x_3098_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3103_, lean_object* v_00_u03b2_3104_, lean_object* v_x_3105_, lean_object* v_x_3106_, lean_object* v_x_3107_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3103_, v_x_3105_, v_x_3106_, v_x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3109_, lean_object* v_00_u03b2_3110_, lean_object* v_x_3111_, lean_object* v_x_3112_, lean_object* v_x_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3109_, v_00_u03b2_3110_, v_x_3111_, v_x_3112_, v_x_3113_);
lean_dec_ref(v___x_3109_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3115_, lean_object* v_rootNew_3116_, uint8_t v_a_3117_, lean_object* v_b_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3115_, v_rootNew_3116_, v_a_3117_, v_b_3118_, v___y_3119_, v___y_3123_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3131_, lean_object* v_rootNew_3132_, lean_object* v_a_3133_, lean_object* v_b_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
uint8_t v_a_28348__boxed_3146_; lean_object* v_res_3147_; 
v_a_28348__boxed_3146_ = lean_unbox(v_a_3133_);
v_res_3147_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3131_, v_rootNew_3132_, v_a_28348__boxed_3146_, v_b_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v_lhs_3131_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3148_, lean_object* v_00_u03b2_3149_, lean_object* v_x_3150_, size_t v_x_3151_, lean_object* v_x_3152_){
_start:
{
lean_object* v___x_3153_; 
lean_inc_ref(v_x_3150_);
v___x_3153_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3148_, v_x_3150_, v_x_3151_, v_x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3154_, lean_object* v_00_u03b2_3155_, lean_object* v_x_3156_, lean_object* v_x_3157_, lean_object* v_x_3158_){
_start:
{
size_t v_x_28388__boxed_3159_; lean_object* v_res_3160_; 
v_x_28388__boxed_3159_ = lean_unbox_usize(v_x_3157_);
lean_dec(v_x_3157_);
v_res_3160_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3154_, v_00_u03b2_3155_, v_x_3156_, v_x_28388__boxed_3159_, v_x_3158_);
lean_dec_ref(v_x_3156_);
lean_dec_ref(v___x_3154_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3161_, lean_object* v_00_u03b2_3162_, lean_object* v_x_3163_, size_t v_x_3164_, size_t v_x_3165_, lean_object* v_x_3166_, lean_object* v_x_3167_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3161_, v_x_3163_, v_x_3164_, v_x_3165_, v_x_3166_, v_x_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3169_, lean_object* v_00_u03b2_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_, lean_object* v_x_3173_, lean_object* v_x_3174_, lean_object* v_x_3175_){
_start:
{
size_t v_x_28402__boxed_3176_; size_t v_x_28403__boxed_3177_; lean_object* v_res_3178_; 
v_x_28402__boxed_3176_ = lean_unbox_usize(v_x_3172_);
lean_dec(v_x_3172_);
v_x_28403__boxed_3177_ = lean_unbox_usize(v_x_3173_);
lean_dec(v_x_3173_);
v_res_3178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3169_, v_00_u03b2_3170_, v_x_3171_, v_x_28402__boxed_3176_, v_x_28403__boxed_3177_, v_x_3174_, v_x_3175_);
lean_dec_ref(v___x_3169_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3179_, lean_object* v_00_u03b2_3180_, lean_object* v_keys_3181_, lean_object* v_vals_3182_, lean_object* v_heq_3183_, lean_object* v_i_3184_, lean_object* v_k_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3179_, v_keys_3181_, v_vals_3182_, v_i_3184_, v_k_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3187_, lean_object* v_00_u03b2_3188_, lean_object* v_keys_3189_, lean_object* v_vals_3190_, lean_object* v_heq_3191_, lean_object* v_i_3192_, lean_object* v_k_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3187_, v_00_u03b2_3188_, v_keys_3189_, v_vals_3190_, v_heq_3191_, v_i_3192_, v_k_3193_);
lean_dec_ref(v_vals_3190_);
lean_dec_ref(v_keys_3189_);
lean_dec_ref(v___x_3187_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3195_, lean_object* v_00_u03b2_3196_, lean_object* v_n_3197_, lean_object* v_k_3198_, lean_object* v_v_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3195_, v_n_3197_, v_k_3198_, v_v_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3201_, lean_object* v_00_u03b2_3202_, lean_object* v_n_3203_, lean_object* v_k_3204_, lean_object* v_v_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3201_, v_00_u03b2_3202_, v_n_3203_, v_k_3204_, v_v_3205_);
lean_dec_ref(v___x_3201_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3207_, lean_object* v_00_u03b2_3208_, size_t v_depth_3209_, lean_object* v_keys_3210_, lean_object* v_vals_3211_, lean_object* v_heq_3212_, lean_object* v_i_3213_, lean_object* v_entries_3214_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3207_, v_depth_3209_, v_keys_3210_, v_vals_3211_, v_i_3213_, v_entries_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3216_, lean_object* v_00_u03b2_3217_, lean_object* v_depth_3218_, lean_object* v_keys_3219_, lean_object* v_vals_3220_, lean_object* v_heq_3221_, lean_object* v_i_3222_, lean_object* v_entries_3223_){
_start:
{
size_t v_depth_boxed_3224_; lean_object* v_res_3225_; 
v_depth_boxed_3224_ = lean_unbox_usize(v_depth_3218_);
lean_dec(v_depth_3218_);
v_res_3225_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3216_, v_00_u03b2_3217_, v_depth_boxed_3224_, v_keys_3219_, v_vals_3220_, v_heq_3221_, v_i_3222_, v_entries_3223_);
lean_dec_ref(v_vals_3220_);
lean_dec_ref(v_keys_3219_);
lean_dec_ref(v___x_3216_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3226_, lean_object* v_00_u03b2_3227_, lean_object* v_x_3228_, lean_object* v_x_3229_, lean_object* v_x_3230_, lean_object* v_x_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3226_, v_x_3228_, v_x_3229_, v_x_3230_, v_x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3233_, lean_object* v_00_u03b2_3234_, lean_object* v_x_3235_, lean_object* v_x_3236_, lean_object* v_x_3237_, lean_object* v_x_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3233_, v_00_u03b2_3234_, v_x_3235_, v_x_3236_, v_x_3237_, v_x_3238_);
lean_dec_ref(v___x_3233_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3240_, lean_object* v_b_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
if (lean_obj_tag(v_as_x27_3240_) == 0)
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v_b_3241_);
return v___x_3253_;
}
else
{
lean_object* v_head_3254_; lean_object* v_tail_3255_; lean_object* v___x_3256_; 
v_head_3254_ = lean_ctor_get(v_as_x27_3240_, 0);
v_tail_3255_ = lean_ctor_get(v_as_x27_3240_, 1);
lean_inc(v_head_3254_);
v___x_3256_ = l_Lean_Meta_Grind_propagateUp(v_head_3254_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v___x_3257_; 
lean_dec_ref(v___x_3256_);
v___x_3257_ = lean_box(0);
v_as_x27_3240_ = v_tail_3255_;
v_b_3241_ = v___x_3257_;
goto _start;
}
else
{
return v___x_3256_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3259_, lean_object* v_b_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3259_, v_b_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec(v_as_x27_3259_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3273_, lean_object* v_b_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
if (lean_obj_tag(v_as_x27_3273_) == 0)
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_b_3274_);
return v___x_3286_;
}
else
{
lean_object* v_head_3287_; lean_object* v_tail_3288_; lean_object* v___x_3289_; 
v_head_3287_ = lean_ctor_get(v_as_x27_3273_, 0);
v_tail_3288_ = lean_ctor_get(v_as_x27_3273_, 1);
lean_inc(v_head_3287_);
v___x_3289_ = l_Lean_Meta_Grind_propagateDown(v_head_3287_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v___x_3290_; 
lean_dec_ref(v___x_3289_);
v___x_3290_ = lean_box(0);
v_as_x27_3273_ = v_tail_3288_;
v_b_3274_ = v___x_3290_;
goto _start;
}
else
{
return v___x_3289_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3292_, lean_object* v_b_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3292_, v_b_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec(v_as_x27_3292_);
return v_res_3305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_cls_3309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3310_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3311_ = l_Lean_Name_append(v___x_3310_, v_cls_3309_);
return v___x_3311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3314_ = l_Lean_stringToMessageData(v___x_3313_);
return v___x_3314_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3317_ = l_Lean_stringToMessageData(v___x_3316_);
return v___x_3317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3320_ = l_Lean_stringToMessageData(v___x_3319_);
return v___x_3320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3323_ = l_Lean_stringToMessageData(v___x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3324_, uint8_t v_isHEq_3325_, lean_object* v_lhs_3326_, lean_object* v_rhs_3327_, lean_object* v_lhsNode_3328_, lean_object* v_rhsNode_3329_, lean_object* v_lhsRoot_3330_, lean_object* v_rhsRoot_3331_, uint8_t v_flipped_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; uint8_t v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; uint8_t v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; uint8_t v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; uint8_t v___y_3429_; uint8_t v___y_3430_; lean_object* v___y_3431_; uint8_t v___y_3432_; uint8_t v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; uint8_t v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; uint8_t v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; uint8_t v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; uint8_t v___y_3494_; lean_object* v___y_3495_; uint8_t v___y_3496_; lean_object* v___y_3497_; uint8_t v___y_3498_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; uint8_t v___y_3509_; uint8_t v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v_options_3582_; lean_object* v_inheritedTraceOptions_3583_; uint8_t v_hasTrace_3584_; lean_object* v_cls_3585_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v_fns_u2082_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v_fns_u2081_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; 
v_options_3582_ = lean_ctor_get(v_a_3341_, 2);
v_inheritedTraceOptions_3583_ = lean_ctor_get(v_a_3341_, 13);
v_hasTrace_3584_ = lean_ctor_get_uint8(v_options_3582_, sizeof(void*)*1);
v_cls_3585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3584_ == 0)
{
v___y_3704_ = v_a_3333_;
v___y_3705_ = v_a_3334_;
v___y_3706_ = v_a_3335_;
v___y_3707_ = v_a_3336_;
v___y_3708_ = v_a_3337_;
v___y_3709_ = v_a_3338_;
v___y_3710_ = v_a_3339_;
v___y_3711_ = v_a_3340_;
v___y_3712_ = v_a_3341_;
v___y_3713_ = v_a_3342_;
goto v___jp_3703_;
}
else
{
lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3784_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3785_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3583_, v_options_3582_, v___x_3784_);
if (v___x_3785_ == 0)
{
v___y_3704_ = v_a_3333_;
v___y_3705_ = v_a_3334_;
v___y_3706_ = v_a_3335_;
v___y_3707_ = v_a_3336_;
v___y_3708_ = v_a_3337_;
v___y_3709_ = v_a_3338_;
v___y_3710_ = v_a_3339_;
v___y_3711_ = v_a_3340_;
v___y_3712_ = v_a_3341_;
v___y_3713_ = v_a_3342_;
goto v___jp_3703_;
}
else
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_Meta_Grind_updateLastTag(v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v___x_3787_; 
lean_dec_ref(v___x_3786_);
lean_inc_ref(v_lhs_3326_);
v___x_3787_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3326_, v_a_3333_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3789_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref(v___x_3787_);
lean_inc_ref(v_rhs_3327_);
v___x_3789_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3327_, v_a_3333_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
lean_ctor_set(v___x_3792_, 1, v_a_3788_);
v___x_3793_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3792_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
v___x_3795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3794_);
lean_ctor_set(v___x_3795_, 1, v_a_3790_);
v___x_3796_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3585_, v___x_3795_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_dec_ref(v___x_3796_);
v___y_3704_ = v_a_3333_;
v___y_3705_ = v_a_3334_;
v___y_3706_ = v_a_3335_;
v___y_3707_ = v_a_3336_;
v___y_3708_ = v_a_3337_;
v___y_3709_ = v_a_3338_;
v___y_3710_ = v_a_3339_;
v___y_3711_ = v_a_3340_;
v___y_3712_ = v_a_3341_;
v___y_3713_ = v_a_3342_;
goto v___jp_3703_;
}
else
{
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhsNode_3328_);
lean_dec_ref(v_rhs_3327_);
lean_dec_ref(v_lhs_3326_);
lean_dec_ref(v_proof_3324_);
return v___x_3796_;
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_a_3788_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhsNode_3328_);
lean_dec_ref(v_rhs_3327_);
lean_dec_ref(v_lhs_3326_);
lean_dec_ref(v_proof_3324_);
v_a_3797_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3789_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3789_);
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
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhsNode_3328_);
lean_dec_ref(v_rhs_3327_);
lean_dec_ref(v_lhs_3326_);
lean_dec_ref(v_proof_3324_);
v_a_3805_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3787_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3787_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhsNode_3328_);
lean_dec_ref(v_rhs_3327_);
lean_dec_ref(v_lhs_3326_);
lean_dec_ref(v_proof_3324_);
return v___x_3786_;
}
}
}
v___jp_3344_:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3351_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3387_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3387_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3387_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
uint8_t v___x_3366_; 
v___x_3366_ = lean_unbox(v_a_3362_);
lean_dec(v_a_3362_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_del_object(v___x_3364_);
v___x_3367_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3347_);
lean_dec(v___y_3347_);
v___x_3368_ = lean_box(0);
v___x_3369_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3367_, v___x_3368_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v___x_3367_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v___x_3370_; 
lean_dec_ref(v___x_3369_);
v___x_3370_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3345_, v___x_3368_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v___x_3371_; 
lean_dec_ref(v___x_3370_);
v___x_3371_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3350_, v___y_3349_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec_ref(v___y_3349_);
lean_dec_ref(v___y_3350_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; 
lean_dec_ref(v___x_3371_);
v___x_3372_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3348_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3381_; 
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3381_ == 0)
{
lean_object* v_unused_3382_; 
v_unused_3382_ = lean_ctor_get(v___x_3372_, 0);
lean_dec(v_unused_3382_);
v___x_3374_ = v___x_3372_;
v_isShared_3375_ = v_isSharedCheck_3381_;
goto v_resetjp_3373_;
}
else
{
lean_dec(v___x_3372_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3381_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
uint8_t v___x_3376_; 
v___x_3376_ = l_Lean_Expr_isTrue(v___y_3346_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3378_; 
lean_dec(v___y_3345_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3368_);
v___x_3378_ = v___x_3374_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3368_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
else
{
lean_object* v___x_3380_; 
lean_del_object(v___x_3374_);
v___x_3380_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3345_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v___y_3345_);
return v___x_3380_;
}
}
}
else
{
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
return v___x_3372_;
}
}
else
{
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
return v___x_3371_;
}
}
else
{
lean_dec_ref(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
return v___x_3370_;
}
}
else
{
lean_dec_ref(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
return v___x_3369_;
}
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
lean_dec_ref(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
v___x_3383_ = lean_box(0);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3383_);
v___x_3385_ = v___x_3364_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
v_a_3388_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3361_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3361_);
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
v___jp_3396_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_inc_ref(v___y_3422_);
v___x_3433_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3433_, 0, v___y_3422_);
lean_ctor_set(v___x_3433_, 1, v___y_3420_);
lean_ctor_set(v___x_3433_, 2, v___y_3423_);
lean_ctor_set(v___x_3433_, 3, v___y_3406_);
lean_ctor_set(v___x_3433_, 4, v___y_3417_);
lean_ctor_set(v___x_3433_, 5, v___y_3412_);
lean_ctor_set(v___x_3433_, 6, v___y_3408_);
lean_ctor_set(v___x_3433_, 7, v___y_3416_);
lean_ctor_set(v___x_3433_, 8, v___y_3409_);
lean_ctor_set(v___x_3433_, 9, v___y_3415_);
lean_ctor_set(v___x_3433_, 10, v___y_3418_);
lean_ctor_set(v___x_3433_, 11, v___y_3431_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*12, v___y_3426_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*12 + 1, v___y_3397_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*12 + 2, v___y_3429_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*12 + 3, v___y_3400_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*12 + 4, v___y_3432_);
lean_ctor_set_uint8(v___x_3433_, sizeof(void*)*12 + 5, v___y_3430_);
lean_inc_ref(v___y_3427_);
v___x_3434_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3427_, v___x_3433_, v___y_3424_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v___x_3435_; 
lean_dec_ref(v___x_3434_);
lean_inc_ref(v___y_3421_);
v___x_3435_ = l_Lean_Meta_Grind_propagateBeta(v___y_3421_, v___y_3407_, v___y_3424_, v___y_3402_, v___y_3410_, v___y_3401_, v___y_3405_, v___y_3428_, v___y_3399_, v___y_3411_, v___y_3398_, v___y_3403_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v___x_3436_; 
lean_dec_ref(v___x_3435_);
lean_inc_ref(v___y_3413_);
v___x_3436_ = l_Lean_Meta_Grind_propagateBeta(v___y_3413_, v___y_3425_, v___y_3424_, v___y_3402_, v___y_3410_, v___y_3401_, v___y_3405_, v___y_3428_, v___y_3399_, v___y_3411_, v___y_3398_, v___y_3403_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v___x_3437_; 
lean_dec_ref(v___x_3436_);
v___x_3437_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3331_, v_lhsRoot_3330_, v___y_3424_, v___y_3399_, v___y_3411_, v___y_3398_, v___y_3403_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3414_, v___y_3424_);
lean_dec_ref(v___y_3414_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v___x_3440_; 
lean_dec_ref(v___x_3439_);
lean_inc_ref(v___y_3427_);
v___x_3440_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3404_, v___y_3427_, v___y_3424_, v___y_3402_, v___y_3410_, v___y_3401_, v___y_3405_, v___y_3428_, v___y_3399_, v___y_3411_, v___y_3398_, v___y_3403_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v___x_3441_; 
lean_dec_ref(v___x_3440_);
v___x_3441_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3424_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; uint8_t v___x_3443_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
v___x_3443_ = lean_unbox(v_a_3442_);
lean_dec(v_a_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; 
v___x_3444_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3422_, v___y_3424_, v___y_3402_, v___y_3410_, v___y_3401_, v___y_3405_, v___y_3428_, v___y_3399_, v___y_3411_, v___y_3398_, v___y_3403_);
lean_dec_ref(v___y_3422_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_dec_ref(v___x_3444_);
v___y_3345_ = v___y_3419_;
v___y_3346_ = v___y_3427_;
v___y_3347_ = v___y_3404_;
v___y_3348_ = v_a_3438_;
v___y_3349_ = v___y_3413_;
v___y_3350_ = v___y_3421_;
v___y_3351_ = v___y_3424_;
v___y_3352_ = v___y_3402_;
v___y_3353_ = v___y_3410_;
v___y_3354_ = v___y_3401_;
v___y_3355_ = v___y_3405_;
v___y_3356_ = v___y_3428_;
v___y_3357_ = v___y_3399_;
v___y_3358_ = v___y_3411_;
v___y_3359_ = v___y_3398_;
v___y_3360_ = v___y_3403_;
goto v___jp_3344_;
}
else
{
lean_dec(v_a_3438_);
lean_dec_ref(v___y_3427_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3404_);
return v___x_3444_;
}
}
else
{
lean_dec_ref(v___y_3422_);
v___y_3345_ = v___y_3419_;
v___y_3346_ = v___y_3427_;
v___y_3347_ = v___y_3404_;
v___y_3348_ = v_a_3438_;
v___y_3349_ = v___y_3413_;
v___y_3350_ = v___y_3421_;
v___y_3351_ = v___y_3424_;
v___y_3352_ = v___y_3402_;
v___y_3353_ = v___y_3410_;
v___y_3354_ = v___y_3401_;
v___y_3355_ = v___y_3405_;
v___y_3356_ = v___y_3428_;
v___y_3357_ = v___y_3399_;
v___y_3358_ = v___y_3411_;
v___y_3359_ = v___y_3398_;
v___y_3360_ = v___y_3403_;
goto v___jp_3344_;
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec(v_a_3438_);
lean_dec_ref(v___y_3427_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3404_);
v_a_3445_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3441_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3441_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_dec(v_a_3438_);
lean_dec_ref(v___y_3427_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3404_);
return v___x_3440_;
}
}
else
{
lean_dec(v_a_3438_);
lean_dec_ref(v___y_3427_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3404_);
return v___x_3439_;
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref(v___y_3427_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3404_);
v_a_3453_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3437_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3437_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
else
{
lean_dec_ref(v___y_3427_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3404_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
return v___x_3436_;
}
}
else
{
lean_dec_ref(v___y_3427_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3404_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
return v___x_3435_;
}
}
else
{
lean_dec_ref(v___y_3427_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3404_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
return v___x_3434_;
}
}
v___jp_3461_:
{
if (v_isHEq_3325_ == 0)
{
if (v___y_3478_ == 0)
{
v___y_3397_ = v___y_3462_;
v___y_3398_ = v___y_3464_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3498_;
v___y_3401_ = v___y_3465_;
v___y_3402_ = v___y_3466_;
v___y_3403_ = v___y_3467_;
v___y_3404_ = v___y_3470_;
v___y_3405_ = v___y_3469_;
v___y_3406_ = v___y_3468_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3473_;
v___y_3409_ = v___y_3474_;
v___y_3410_ = v___y_3475_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3477_;
v___y_3413_ = v___y_3479_;
v___y_3414_ = v___y_3480_;
v___y_3415_ = v___y_3481_;
v___y_3416_ = v___y_3482_;
v___y_3417_ = v___y_3483_;
v___y_3418_ = v___y_3484_;
v___y_3419_ = v___y_3485_;
v___y_3420_ = v___y_3486_;
v___y_3421_ = v___y_3487_;
v___y_3422_ = v___y_3488_;
v___y_3423_ = v___y_3489_;
v___y_3424_ = v___y_3490_;
v___y_3425_ = v___y_3492_;
v___y_3426_ = v___y_3491_;
v___y_3427_ = v___y_3493_;
v___y_3428_ = v___y_3495_;
v___y_3429_ = v___y_3494_;
v___y_3430_ = v___y_3496_;
v___y_3431_ = v___y_3497_;
v___y_3432_ = v___y_3472_;
goto v___jp_3396_;
}
else
{
v___y_3397_ = v___y_3462_;
v___y_3398_ = v___y_3464_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3498_;
v___y_3401_ = v___y_3465_;
v___y_3402_ = v___y_3466_;
v___y_3403_ = v___y_3467_;
v___y_3404_ = v___y_3470_;
v___y_3405_ = v___y_3469_;
v___y_3406_ = v___y_3468_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3473_;
v___y_3409_ = v___y_3474_;
v___y_3410_ = v___y_3475_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3477_;
v___y_3413_ = v___y_3479_;
v___y_3414_ = v___y_3480_;
v___y_3415_ = v___y_3481_;
v___y_3416_ = v___y_3482_;
v___y_3417_ = v___y_3483_;
v___y_3418_ = v___y_3484_;
v___y_3419_ = v___y_3485_;
v___y_3420_ = v___y_3486_;
v___y_3421_ = v___y_3487_;
v___y_3422_ = v___y_3488_;
v___y_3423_ = v___y_3489_;
v___y_3424_ = v___y_3490_;
v___y_3425_ = v___y_3492_;
v___y_3426_ = v___y_3491_;
v___y_3427_ = v___y_3493_;
v___y_3428_ = v___y_3495_;
v___y_3429_ = v___y_3494_;
v___y_3430_ = v___y_3496_;
v___y_3431_ = v___y_3497_;
v___y_3432_ = v___y_3478_;
goto v___jp_3396_;
}
}
else
{
v___y_3397_ = v___y_3462_;
v___y_3398_ = v___y_3464_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3498_;
v___y_3401_ = v___y_3465_;
v___y_3402_ = v___y_3466_;
v___y_3403_ = v___y_3467_;
v___y_3404_ = v___y_3470_;
v___y_3405_ = v___y_3469_;
v___y_3406_ = v___y_3468_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3473_;
v___y_3409_ = v___y_3474_;
v___y_3410_ = v___y_3475_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3477_;
v___y_3413_ = v___y_3479_;
v___y_3414_ = v___y_3480_;
v___y_3415_ = v___y_3481_;
v___y_3416_ = v___y_3482_;
v___y_3417_ = v___y_3483_;
v___y_3418_ = v___y_3484_;
v___y_3419_ = v___y_3485_;
v___y_3420_ = v___y_3486_;
v___y_3421_ = v___y_3487_;
v___y_3422_ = v___y_3488_;
v___y_3423_ = v___y_3489_;
v___y_3424_ = v___y_3490_;
v___y_3425_ = v___y_3492_;
v___y_3426_ = v___y_3491_;
v___y_3427_ = v___y_3493_;
v___y_3428_ = v___y_3495_;
v___y_3429_ = v___y_3494_;
v___y_3430_ = v___y_3496_;
v___y_3431_ = v___y_3497_;
v___y_3432_ = v_isHEq_3325_;
goto v___jp_3396_;
}
}
v___jp_3499_:
{
lean_object* v___x_3522_; 
v___x_3522_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3504_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_dec_ref(v___x_3522_);
v___x_3523_ = lean_st_ref_get(v___y_3512_);
v___x_3524_ = lean_st_ref_get(v___y_3512_);
lean_inc_ref(v___y_3511_);
v___x_3525_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3524_, v___y_3511_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
lean_dec(v___x_3524_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v_self_3527_; lean_object* v_root_3528_; lean_object* v_congr_3529_; lean_object* v_target_x3f_3530_; lean_object* v_proof_x3f_3531_; uint8_t v_flipped_3532_; lean_object* v_size_3533_; uint8_t v_interpreted_3534_; uint8_t v_ctor_3535_; uint8_t v_hasLambdas_3536_; uint8_t v_heqProofs_3537_; lean_object* v_idx_3538_; lean_object* v_generation_3539_; lean_object* v_mt_3540_; lean_object* v_sTerms_3541_; uint8_t v_funCC_3542_; lean_object* v_ematchDiagSource_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3572_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref(v___x_3525_);
v_self_3527_ = lean_ctor_get(v_a_3526_, 0);
v_root_3528_ = lean_ctor_get(v_a_3526_, 2);
v_congr_3529_ = lean_ctor_get(v_a_3526_, 3);
v_target_x3f_3530_ = lean_ctor_get(v_a_3526_, 4);
v_proof_x3f_3531_ = lean_ctor_get(v_a_3526_, 5);
v_flipped_3532_ = lean_ctor_get_uint8(v_a_3526_, sizeof(void*)*12);
v_size_3533_ = lean_ctor_get(v_a_3526_, 6);
v_interpreted_3534_ = lean_ctor_get_uint8(v_a_3526_, sizeof(void*)*12 + 1);
v_ctor_3535_ = lean_ctor_get_uint8(v_a_3526_, sizeof(void*)*12 + 2);
v_hasLambdas_3536_ = lean_ctor_get_uint8(v_a_3526_, sizeof(void*)*12 + 3);
v_heqProofs_3537_ = lean_ctor_get_uint8(v_a_3526_, sizeof(void*)*12 + 4);
v_idx_3538_ = lean_ctor_get(v_a_3526_, 7);
v_generation_3539_ = lean_ctor_get(v_a_3526_, 8);
v_mt_3540_ = lean_ctor_get(v_a_3526_, 9);
v_sTerms_3541_ = lean_ctor_get(v_a_3526_, 10);
v_funCC_3542_ = lean_ctor_get_uint8(v_a_3526_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3543_ = lean_ctor_get(v_a_3526_, 11);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_a_3526_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v_a_3526_, 1);
lean_dec(v_unused_3573_);
v___x_3545_ = v_a_3526_;
v_isShared_3546_ = v_isSharedCheck_3572_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_ematchDiagSource_3543_);
lean_inc(v_sTerms_3541_);
lean_inc(v_mt_3540_);
lean_inc(v_generation_3539_);
lean_inc(v_idx_3538_);
lean_inc(v_size_3533_);
lean_inc(v_proof_x3f_3531_);
lean_inc(v_target_x3f_3530_);
lean_inc(v_congr_3529_);
lean_inc(v_root_3528_);
lean_inc(v_self_3527_);
lean_dec(v_a_3526_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3572_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v_self_3547_; lean_object* v_next_3548_; lean_object* v_root_3549_; lean_object* v_congr_3550_; lean_object* v_target_x3f_3551_; lean_object* v_proof_x3f_3552_; uint8_t v_flipped_3553_; lean_object* v_size_3554_; uint8_t v_interpreted_3555_; uint8_t v_ctor_3556_; uint8_t v_hasLambdas_3557_; uint8_t v_heqProofs_3558_; lean_object* v_idx_3559_; lean_object* v_generation_3560_; lean_object* v_mt_3561_; lean_object* v_sTerms_3562_; uint8_t v_funCC_3563_; lean_object* v_ematchDiagSource_3564_; lean_object* v___x_3566_; 
v_self_3547_ = lean_ctor_get(v_rhsRoot_3331_, 0);
v_next_3548_ = lean_ctor_get(v_rhsRoot_3331_, 1);
v_root_3549_ = lean_ctor_get(v_rhsRoot_3331_, 2);
v_congr_3550_ = lean_ctor_get(v_rhsRoot_3331_, 3);
v_target_x3f_3551_ = lean_ctor_get(v_rhsRoot_3331_, 4);
v_proof_x3f_3552_ = lean_ctor_get(v_rhsRoot_3331_, 5);
v_flipped_3553_ = lean_ctor_get_uint8(v_rhsRoot_3331_, sizeof(void*)*12);
v_size_3554_ = lean_ctor_get(v_rhsRoot_3331_, 6);
v_interpreted_3555_ = lean_ctor_get_uint8(v_rhsRoot_3331_, sizeof(void*)*12 + 1);
v_ctor_3556_ = lean_ctor_get_uint8(v_rhsRoot_3331_, sizeof(void*)*12 + 2);
v_hasLambdas_3557_ = lean_ctor_get_uint8(v_rhsRoot_3331_, sizeof(void*)*12 + 3);
v_heqProofs_3558_ = lean_ctor_get_uint8(v_rhsRoot_3331_, sizeof(void*)*12 + 4);
v_idx_3559_ = lean_ctor_get(v_rhsRoot_3331_, 7);
v_generation_3560_ = lean_ctor_get(v_rhsRoot_3331_, 8);
v_mt_3561_ = lean_ctor_get(v_rhsRoot_3331_, 9);
v_sTerms_3562_ = lean_ctor_get(v_rhsRoot_3331_, 10);
v_funCC_3563_ = lean_ctor_get_uint8(v_rhsRoot_3331_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3564_ = lean_ctor_get(v_rhsRoot_3331_, 11);
lean_inc_ref(v_next_3548_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 1, v_next_3548_);
v___x_3566_ = v___x_3545_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_self_3527_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_next_3548_);
lean_ctor_set(v_reuseFailAlloc_3571_, 2, v_root_3528_);
lean_ctor_set(v_reuseFailAlloc_3571_, 3, v_congr_3529_);
lean_ctor_set(v_reuseFailAlloc_3571_, 4, v_target_x3f_3530_);
lean_ctor_set(v_reuseFailAlloc_3571_, 5, v_proof_x3f_3531_);
lean_ctor_set(v_reuseFailAlloc_3571_, 6, v_size_3533_);
lean_ctor_set(v_reuseFailAlloc_3571_, 7, v_idx_3538_);
lean_ctor_set(v_reuseFailAlloc_3571_, 8, v_generation_3539_);
lean_ctor_set(v_reuseFailAlloc_3571_, 9, v_mt_3540_);
lean_ctor_set(v_reuseFailAlloc_3571_, 10, v_sTerms_3541_);
lean_ctor_set(v_reuseFailAlloc_3571_, 11, v_ematchDiagSource_3543_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, sizeof(void*)*12, v_flipped_3532_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, sizeof(void*)*12 + 1, v_interpreted_3534_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, sizeof(void*)*12 + 2, v_ctor_3535_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, sizeof(void*)*12 + 3, v_hasLambdas_3536_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, sizeof(void*)*12 + 4, v_heqProofs_3537_);
lean_ctor_set_uint8(v_reuseFailAlloc_3571_, sizeof(void*)*12 + 5, v_funCC_3542_);
v___x_3566_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3567_; 
v___x_3567_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3500_, v___x_3566_, v___y_3512_);
if (lean_obj_tag(v___x_3567_) == 0)
{
uint8_t v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec_ref(v___x_3567_);
v___x_3568_ = 0;
v___x_3569_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3523_, v_lhs_3326_, v___x_3568_);
lean_dec(v___x_3523_);
v___x_3570_ = lean_nat_add(v_size_3554_, v___y_3507_);
lean_dec(v___y_3507_);
if (v_hasLambdas_3557_ == 0)
{
lean_inc(v_ematchDiagSource_3564_);
lean_inc_ref(v_root_3549_);
lean_inc_ref(v_self_3547_);
lean_inc(v_sTerms_3562_);
lean_inc(v_target_x3f_3551_);
lean_inc(v_idx_3559_);
lean_inc(v_mt_3561_);
lean_inc(v_proof_x3f_3552_);
lean_inc(v_generation_3560_);
lean_inc_ref(v_congr_3550_);
v___y_3462_ = v_interpreted_3555_;
v___y_3463_ = v___y_3518_;
v___y_3464_ = v___y_3520_;
v___y_3465_ = v___y_3515_;
v___y_3466_ = v___y_3513_;
v___y_3467_ = v___y_3521_;
v___y_3468_ = v_congr_3550_;
v___y_3469_ = v___y_3516_;
v___y_3470_ = v___y_3504_;
v___y_3471_ = v___y_3508_;
v___y_3472_ = v___y_3510_;
v___y_3473_ = v___x_3570_;
v___y_3474_ = v_generation_3560_;
v___y_3475_ = v___y_3514_;
v___y_3476_ = v___y_3519_;
v___y_3477_ = v_proof_x3f_3552_;
v___y_3478_ = v_heqProofs_3558_;
v___y_3479_ = v___y_3506_;
v___y_3480_ = v___y_3511_;
v___y_3481_ = v_mt_3561_;
v___y_3482_ = v_idx_3559_;
v___y_3483_ = v_target_x3f_3551_;
v___y_3484_ = v_sTerms_3562_;
v___y_3485_ = v___x_3569_;
v___y_3486_ = v___y_3502_;
v___y_3487_ = v___y_3505_;
v___y_3488_ = v_self_3547_;
v___y_3489_ = v_root_3549_;
v___y_3490_ = v___y_3512_;
v___y_3491_ = v_flipped_3553_;
v___y_3492_ = v___y_3501_;
v___y_3493_ = v___y_3503_;
v___y_3494_ = v_ctor_3556_;
v___y_3495_ = v___y_3517_;
v___y_3496_ = v_funCC_3563_;
v___y_3497_ = v_ematchDiagSource_3564_;
v___y_3498_ = v___y_3509_;
goto v___jp_3461_;
}
else
{
lean_inc(v_ematchDiagSource_3564_);
lean_inc_ref(v_root_3549_);
lean_inc_ref(v_self_3547_);
lean_inc(v_sTerms_3562_);
lean_inc(v_target_x3f_3551_);
lean_inc(v_idx_3559_);
lean_inc(v_mt_3561_);
lean_inc(v_proof_x3f_3552_);
lean_inc(v_generation_3560_);
lean_inc_ref(v_congr_3550_);
v___y_3462_ = v_interpreted_3555_;
v___y_3463_ = v___y_3518_;
v___y_3464_ = v___y_3520_;
v___y_3465_ = v___y_3515_;
v___y_3466_ = v___y_3513_;
v___y_3467_ = v___y_3521_;
v___y_3468_ = v_congr_3550_;
v___y_3469_ = v___y_3516_;
v___y_3470_ = v___y_3504_;
v___y_3471_ = v___y_3508_;
v___y_3472_ = v___y_3510_;
v___y_3473_ = v___x_3570_;
v___y_3474_ = v_generation_3560_;
v___y_3475_ = v___y_3514_;
v___y_3476_ = v___y_3519_;
v___y_3477_ = v_proof_x3f_3552_;
v___y_3478_ = v_heqProofs_3558_;
v___y_3479_ = v___y_3506_;
v___y_3480_ = v___y_3511_;
v___y_3481_ = v_mt_3561_;
v___y_3482_ = v_idx_3559_;
v___y_3483_ = v_target_x3f_3551_;
v___y_3484_ = v_sTerms_3562_;
v___y_3485_ = v___x_3569_;
v___y_3486_ = v___y_3502_;
v___y_3487_ = v___y_3505_;
v___y_3488_ = v_self_3547_;
v___y_3489_ = v_root_3549_;
v___y_3490_ = v___y_3512_;
v___y_3491_ = v_flipped_3553_;
v___y_3492_ = v___y_3501_;
v___y_3493_ = v___y_3503_;
v___y_3494_ = v_ctor_3556_;
v___y_3495_ = v___y_3517_;
v___y_3496_ = v_funCC_3563_;
v___y_3497_ = v_ematchDiagSource_3564_;
v___y_3498_ = v_hasLambdas_3557_;
goto v___jp_3461_;
}
}
else
{
lean_dec(v___x_3523_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_lhs_3326_);
return v___x_3567_;
}
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec(v___x_3523_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_lhs_3326_);
v_a_3574_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3525_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3525_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_lhs_3326_);
return v___x_3522_;
}
}
v___jp_3586_:
{
lean_object* v_self_3602_; lean_object* v_next_3603_; lean_object* v_size_3604_; uint8_t v_hasLambdas_3605_; uint8_t v_heqProofs_3606_; lean_object* v___x_3607_; 
v_self_3602_ = lean_ctor_get(v_lhsRoot_3330_, 0);
v_next_3603_ = lean_ctor_get(v_lhsRoot_3330_, 1);
v_size_3604_ = lean_ctor_get(v_lhsRoot_3330_, 6);
v_hasLambdas_3605_ = lean_ctor_get_uint8(v_lhsRoot_3330_, sizeof(void*)*12 + 3);
v_heqProofs_3606_ = lean_ctor_get_uint8(v_lhsRoot_3330_, sizeof(void*)*12 + 4);
v___x_3607_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3602_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v_root_3609_; lean_object* v___x_3610_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref(v___x_3607_);
v_root_3609_ = lean_ctor_get(v_rhsNode_3329_, 2);
lean_inc_ref_n(v_root_3609_, 2);
lean_dec_ref(v_rhsNode_3329_);
lean_inc_ref(v_lhs_3326_);
v___x_3610_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3326_, v_root_3609_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_options_3611_; uint8_t v_hasTrace_3612_; 
lean_dec_ref(v___x_3610_);
v_options_3611_ = lean_ctor_get(v___y_3600_, 2);
v_hasTrace_3612_ = lean_ctor_get_uint8(v_options_3611_, sizeof(void*)*1);
if (v_hasTrace_3612_ == 0)
{
lean_inc_ref(v_self_3602_);
lean_inc(v_size_3604_);
lean_inc_ref(v_next_3603_);
v___y_3500_ = v___y_3587_;
v___y_3501_ = v_fns_u2082_3591_;
v___y_3502_ = v_next_3603_;
v___y_3503_ = v_root_3609_;
v___y_3504_ = v_a_3608_;
v___y_3505_ = v___y_3589_;
v___y_3506_ = v___y_3588_;
v___y_3507_ = v_size_3604_;
v___y_3508_ = v___y_3590_;
v___y_3509_ = v_hasLambdas_3605_;
v___y_3510_ = v_heqProofs_3606_;
v___y_3511_ = v_self_3602_;
v___y_3512_ = v___y_3592_;
v___y_3513_ = v___y_3593_;
v___y_3514_ = v___y_3594_;
v___y_3515_ = v___y_3595_;
v___y_3516_ = v___y_3596_;
v___y_3517_ = v___y_3597_;
v___y_3518_ = v___y_3598_;
v___y_3519_ = v___y_3599_;
v___y_3520_ = v___y_3600_;
v___y_3521_ = v___y_3601_;
goto v___jp_3499_;
}
else
{
lean_object* v_inheritedTraceOptions_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; 
v_inheritedTraceOptions_3613_ = lean_ctor_get(v___y_3600_, 13);
v___x_3614_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3615_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3613_, v_options_3611_, v___x_3614_);
if (v___x_3615_ == 0)
{
lean_inc_ref(v_self_3602_);
lean_inc(v_size_3604_);
lean_inc_ref(v_next_3603_);
v___y_3500_ = v___y_3587_;
v___y_3501_ = v_fns_u2082_3591_;
v___y_3502_ = v_next_3603_;
v___y_3503_ = v_root_3609_;
v___y_3504_ = v_a_3608_;
v___y_3505_ = v___y_3589_;
v___y_3506_ = v___y_3588_;
v___y_3507_ = v_size_3604_;
v___y_3508_ = v___y_3590_;
v___y_3509_ = v_hasLambdas_3605_;
v___y_3510_ = v_heqProofs_3606_;
v___y_3511_ = v_self_3602_;
v___y_3512_ = v___y_3592_;
v___y_3513_ = v___y_3593_;
v___y_3514_ = v___y_3594_;
v___y_3515_ = v___y_3595_;
v___y_3516_ = v___y_3596_;
v___y_3517_ = v___y_3597_;
v___y_3518_ = v___y_3598_;
v___y_3519_ = v___y_3599_;
v___y_3520_ = v___y_3600_;
v___y_3521_ = v___y_3601_;
goto v___jp_3499_;
}
else
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Lean_Meta_Grind_updateLastTag(v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v___x_3617_; 
lean_dec_ref(v___x_3616_);
lean_inc_ref(v_lhs_3326_);
v___x_3617_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3326_, v___y_3592_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref(v___x_3617_);
lean_inc_ref(v_root_3609_);
v___x_3619_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3609_, v___y_3592_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
lean_dec_ref(v___x_3619_);
v___x_3621_ = lean_st_ref_get(v___y_3592_);
lean_inc_ref(v_lhs_3326_);
v___x_3622_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3621_, v_lhs_3326_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___x_3621_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___x_3624_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref(v___x_3622_);
v___x_3624_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3623_, v___y_3592_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref(v___x_3624_);
v___x_3626_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v_a_3618_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
lean_ctor_set(v___x_3628_, 1, v_a_3620_);
v___x_3629_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3628_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
lean_ctor_set(v___x_3631_, 1, v_a_3625_);
v___x_3632_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3585_, v___x_3631_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_dec_ref(v___x_3632_);
lean_inc_ref(v_self_3602_);
lean_inc(v_size_3604_);
lean_inc_ref(v_next_3603_);
v___y_3500_ = v___y_3587_;
v___y_3501_ = v_fns_u2082_3591_;
v___y_3502_ = v_next_3603_;
v___y_3503_ = v_root_3609_;
v___y_3504_ = v_a_3608_;
v___y_3505_ = v___y_3589_;
v___y_3506_ = v___y_3588_;
v___y_3507_ = v_size_3604_;
v___y_3508_ = v___y_3590_;
v___y_3509_ = v_hasLambdas_3605_;
v___y_3510_ = v_heqProofs_3606_;
v___y_3511_ = v_self_3602_;
v___y_3512_ = v___y_3592_;
v___y_3513_ = v___y_3593_;
v___y_3514_ = v___y_3594_;
v___y_3515_ = v___y_3595_;
v___y_3516_ = v___y_3596_;
v___y_3517_ = v___y_3597_;
v___y_3518_ = v___y_3598_;
v___y_3519_ = v___y_3599_;
v___y_3520_ = v___y_3600_;
v___y_3521_ = v___y_3601_;
goto v___jp_3499_;
}
else
{
lean_dec_ref(v_root_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_fns_u2082_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_lhs_3326_);
return v___x_3632_;
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v_a_3620_);
lean_dec(v_a_3618_);
lean_dec_ref(v_root_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_fns_u2082_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_lhs_3326_);
v_a_3633_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3624_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3624_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_dec(v_a_3620_);
lean_dec(v_a_3618_);
lean_dec_ref(v_root_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_fns_u2082_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_lhs_3326_);
v_a_3641_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3622_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3622_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
else
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
lean_dec(v_a_3618_);
lean_dec_ref(v_root_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_fns_u2082_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_lhs_3326_);
v_a_3649_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3619_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3619_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec_ref(v_root_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_fns_u2082_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_lhs_3326_);
v_a_3657_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3617_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3617_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
else
{
lean_dec_ref(v_root_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_fns_u2082_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_lhs_3326_);
return v___x_3616_;
}
}
}
}
else
{
lean_dec_ref(v_root_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_fns_u2082_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_lhs_3326_);
return v___x_3610_;
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_dec_ref(v_fns_u2082_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhs_3326_);
v_a_3665_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3607_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3607_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
v___jp_3673_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; 
v___x_3688_ = lean_array_get_size(v___y_3676_);
v___x_3689_ = lean_unsigned_to_nat(0u);
v___x_3690_ = lean_nat_dec_eq(v___x_3688_, v___x_3689_);
if (v___x_3690_ == 0)
{
lean_object* v_self_3691_; lean_object* v___x_3692_; 
v_self_3691_ = lean_ctor_get(v_lhsRoot_3330_, 0);
lean_inc_ref(v_self_3691_);
v___x_3692_ = l_Lean_Meta_Grind_getFnRoots(v_self_3691_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref(v___x_3692_);
v___y_3587_ = v___y_3674_;
v___y_3588_ = v___y_3676_;
v___y_3589_ = v___y_3675_;
v___y_3590_ = v_fns_u2081_3677_;
v_fns_u2082_3591_ = v_a_3693_;
v___y_3592_ = v___y_3678_;
v___y_3593_ = v___y_3679_;
v___y_3594_ = v___y_3680_;
v___y_3595_ = v___y_3681_;
v___y_3596_ = v___y_3682_;
v___y_3597_ = v___y_3683_;
v___y_3598_ = v___y_3684_;
v___y_3599_ = v___y_3685_;
v___y_3600_ = v___y_3686_;
v___y_3601_ = v___y_3687_;
goto v___jp_3586_;
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec_ref(v_fns_u2081_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhs_3326_);
v_a_3694_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3692_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3692_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
else
{
lean_object* v___x_3702_; 
v___x_3702_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3587_ = v___y_3674_;
v___y_3588_ = v___y_3676_;
v___y_3589_ = v___y_3675_;
v___y_3590_ = v_fns_u2081_3677_;
v_fns_u2082_3591_ = v___x_3702_;
v___y_3592_ = v___y_3678_;
v___y_3593_ = v___y_3679_;
v___y_3594_ = v___y_3680_;
v___y_3595_ = v___y_3681_;
v___y_3596_ = v___y_3682_;
v___y_3597_ = v___y_3683_;
v___y_3598_ = v___y_3684_;
v___y_3599_ = v___y_3685_;
v___y_3600_ = v___y_3686_;
v___y_3601_ = v___y_3687_;
goto v___jp_3586_;
}
}
v___jp_3703_:
{
lean_object* v___x_3714_; 
lean_inc_ref(v_lhs_3326_);
v___x_3714_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3326_, v___y_3704_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3782_; 
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; 
v_unused_3783_ = lean_ctor_get(v___x_3714_, 0);
lean_dec(v_unused_3783_);
v___x_3716_ = v___x_3714_;
v_isShared_3717_ = v_isSharedCheck_3782_;
goto v_resetjp_3715_;
}
else
{
lean_dec(v___x_3714_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3782_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v_self_3718_; lean_object* v_next_3719_; lean_object* v_root_3720_; lean_object* v_congr_3721_; lean_object* v_size_3722_; uint8_t v_interpreted_3723_; uint8_t v_ctor_3724_; uint8_t v_hasLambdas_3725_; uint8_t v_heqProofs_3726_; lean_object* v_idx_3727_; lean_object* v_generation_3728_; lean_object* v_mt_3729_; lean_object* v_sTerms_3730_; uint8_t v_funCC_3731_; lean_object* v_ematchDiagSource_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3779_; 
v_self_3718_ = lean_ctor_get(v_lhsNode_3328_, 0);
v_next_3719_ = lean_ctor_get(v_lhsNode_3328_, 1);
v_root_3720_ = lean_ctor_get(v_lhsNode_3328_, 2);
v_congr_3721_ = lean_ctor_get(v_lhsNode_3328_, 3);
v_size_3722_ = lean_ctor_get(v_lhsNode_3328_, 6);
v_interpreted_3723_ = lean_ctor_get_uint8(v_lhsNode_3328_, sizeof(void*)*12 + 1);
v_ctor_3724_ = lean_ctor_get_uint8(v_lhsNode_3328_, sizeof(void*)*12 + 2);
v_hasLambdas_3725_ = lean_ctor_get_uint8(v_lhsNode_3328_, sizeof(void*)*12 + 3);
v_heqProofs_3726_ = lean_ctor_get_uint8(v_lhsNode_3328_, sizeof(void*)*12 + 4);
v_idx_3727_ = lean_ctor_get(v_lhsNode_3328_, 7);
v_generation_3728_ = lean_ctor_get(v_lhsNode_3328_, 8);
v_mt_3729_ = lean_ctor_get(v_lhsNode_3328_, 9);
v_sTerms_3730_ = lean_ctor_get(v_lhsNode_3328_, 10);
v_funCC_3731_ = lean_ctor_get_uint8(v_lhsNode_3328_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3732_ = lean_ctor_get(v_lhsNode_3328_, 11);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_lhsNode_3328_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; lean_object* v_unused_3781_; 
v_unused_3780_ = lean_ctor_get(v_lhsNode_3328_, 5);
lean_dec(v_unused_3780_);
v_unused_3781_ = lean_ctor_get(v_lhsNode_3328_, 4);
lean_dec(v_unused_3781_);
v___x_3734_ = v_lhsNode_3328_;
v_isShared_3735_ = v_isSharedCheck_3779_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_ematchDiagSource_3732_);
lean_inc(v_sTerms_3730_);
lean_inc(v_mt_3729_);
lean_inc(v_generation_3728_);
lean_inc(v_idx_3727_);
lean_inc(v_size_3722_);
lean_inc(v_congr_3721_);
lean_inc(v_root_3720_);
lean_inc(v_next_3719_);
lean_inc(v_self_3718_);
lean_dec(v_lhsNode_3328_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3779_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set_tag(v___x_3716_, 1);
lean_ctor_set(v___x_3716_, 0, v_rhs_3327_);
v___x_3737_ = v___x_3716_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_rhs_3327_);
v___x_3737_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3738_; lean_object* v___x_3740_; 
v___x_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3738_, 0, v_proof_3324_);
lean_inc_ref(v_root_3720_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set(v___x_3734_, 5, v___x_3738_);
lean_ctor_set(v___x_3734_, 4, v___x_3737_);
v___x_3740_ = v___x_3734_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_self_3718_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_next_3719_);
lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_root_3720_);
lean_ctor_set(v_reuseFailAlloc_3777_, 3, v_congr_3721_);
lean_ctor_set(v_reuseFailAlloc_3777_, 4, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3777_, 5, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3777_, 6, v_size_3722_);
lean_ctor_set(v_reuseFailAlloc_3777_, 7, v_idx_3727_);
lean_ctor_set(v_reuseFailAlloc_3777_, 8, v_generation_3728_);
lean_ctor_set(v_reuseFailAlloc_3777_, 9, v_mt_3729_);
lean_ctor_set(v_reuseFailAlloc_3777_, 10, v_sTerms_3730_);
lean_ctor_set(v_reuseFailAlloc_3777_, 11, v_ematchDiagSource_3732_);
lean_ctor_set_uint8(v_reuseFailAlloc_3777_, sizeof(void*)*12 + 1, v_interpreted_3723_);
lean_ctor_set_uint8(v_reuseFailAlloc_3777_, sizeof(void*)*12 + 2, v_ctor_3724_);
lean_ctor_set_uint8(v_reuseFailAlloc_3777_, sizeof(void*)*12 + 3, v_hasLambdas_3725_);
lean_ctor_set_uint8(v_reuseFailAlloc_3777_, sizeof(void*)*12 + 4, v_heqProofs_3726_);
lean_ctor_set_uint8(v_reuseFailAlloc_3777_, sizeof(void*)*12 + 5, v_funCC_3731_);
v___x_3740_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; 
lean_ctor_set_uint8(v___x_3740_, sizeof(void*)*12, v_flipped_3332_);
lean_inc_ref(v_lhs_3326_);
v___x_3741_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3326_, v___x_3740_, v___y_3704_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3742_; 
lean_dec_ref(v___x_3741_);
v___x_3742_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3330_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref(v___x_3742_);
v___x_3744_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3331_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref(v___x_3744_);
v___x_3746_ = lean_array_get_size(v_a_3743_);
v___x_3747_ = lean_unsigned_to_nat(0u);
v___x_3748_ = lean_nat_dec_eq(v___x_3746_, v___x_3747_);
if (v___x_3748_ == 0)
{
lean_object* v_self_3749_; lean_object* v___x_3750_; 
v_self_3749_ = lean_ctor_get(v_rhsRoot_3331_, 0);
lean_inc_ref(v_self_3749_);
v___x_3750_ = l_Lean_Meta_Grind_getFnRoots(v_self_3749_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref(v___x_3750_);
v___y_3674_ = v_root_3720_;
v___y_3675_ = v_a_3743_;
v___y_3676_ = v_a_3745_;
v_fns_u2081_3677_ = v_a_3751_;
v___y_3678_ = v___y_3704_;
v___y_3679_ = v___y_3705_;
v___y_3680_ = v___y_3706_;
v___y_3681_ = v___y_3707_;
v___y_3682_ = v___y_3708_;
v___y_3683_ = v___y_3709_;
v___y_3684_ = v___y_3710_;
v___y_3685_ = v___y_3711_;
v___y_3686_ = v___y_3712_;
v___y_3687_ = v___y_3713_;
goto v___jp_3673_;
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec(v_a_3745_);
lean_dec(v_a_3743_);
lean_dec_ref(v_root_3720_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhs_3326_);
v_a_3752_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3750_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3750_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
else
{
lean_object* v___x_3760_; 
v___x_3760_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3674_ = v_root_3720_;
v___y_3675_ = v_a_3743_;
v___y_3676_ = v_a_3745_;
v_fns_u2081_3677_ = v___x_3760_;
v___y_3678_ = v___y_3704_;
v___y_3679_ = v___y_3705_;
v___y_3680_ = v___y_3706_;
v___y_3681_ = v___y_3707_;
v___y_3682_ = v___y_3708_;
v___y_3683_ = v___y_3709_;
v___y_3684_ = v___y_3710_;
v___y_3685_ = v___y_3711_;
v___y_3686_ = v___y_3712_;
v___y_3687_ = v___y_3713_;
goto v___jp_3673_;
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3743_);
lean_dec_ref(v_root_3720_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhs_3326_);
v_a_3761_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3744_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3744_);
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
lean_dec_ref(v_root_3720_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhs_3326_);
v_a_3769_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3742_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3742_);
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
lean_dec_ref(v_root_3720_);
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhs_3326_);
return v___x_3741_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3331_);
lean_dec_ref(v_lhsRoot_3330_);
lean_dec_ref(v_rhsNode_3329_);
lean_dec_ref(v_lhsNode_3328_);
lean_dec_ref(v_rhs_3327_);
lean_dec_ref(v_lhs_3326_);
lean_dec_ref(v_proof_3324_);
return v___x_3714_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3813_ = _args[0];
lean_object* v_isHEq_3814_ = _args[1];
lean_object* v_lhs_3815_ = _args[2];
lean_object* v_rhs_3816_ = _args[3];
lean_object* v_lhsNode_3817_ = _args[4];
lean_object* v_rhsNode_3818_ = _args[5];
lean_object* v_lhsRoot_3819_ = _args[6];
lean_object* v_rhsRoot_3820_ = _args[7];
lean_object* v_flipped_3821_ = _args[8];
lean_object* v_a_3822_ = _args[9];
lean_object* v_a_3823_ = _args[10];
lean_object* v_a_3824_ = _args[11];
lean_object* v_a_3825_ = _args[12];
lean_object* v_a_3826_ = _args[13];
lean_object* v_a_3827_ = _args[14];
lean_object* v_a_3828_ = _args[15];
lean_object* v_a_3829_ = _args[16];
lean_object* v_a_3830_ = _args[17];
lean_object* v_a_3831_ = _args[18];
lean_object* v_a_3832_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3833_; uint8_t v_flipped_boxed_3834_; lean_object* v_res_3835_; 
v_isHEq_boxed_3833_ = lean_unbox(v_isHEq_3814_);
v_flipped_boxed_3834_ = lean_unbox(v_flipped_3821_);
v_res_3835_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3813_, v_isHEq_boxed_3833_, v_lhs_3815_, v_rhs_3816_, v_lhsNode_3817_, v_rhsNode_3818_, v_lhsRoot_3819_, v_rhsRoot_3820_, v_flipped_boxed_3834_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
lean_dec(v_a_3827_);
lean_dec_ref(v_a_3826_);
lean_dec(v_a_3825_);
lean_dec_ref(v_a_3824_);
lean_dec(v_a_3823_);
lean_dec(v_a_3822_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3836_, lean_object* v_as_x27_3837_, lean_object* v_b_3838_, lean_object* v_a_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3837_, v_b_3838_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3852_, lean_object* v_as_x27_3853_, lean_object* v_b_3854_, lean_object* v_a_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3852_, v_as_x27_3853_, v_b_3854_, v_a_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec(v_as_x27_3853_);
lean_dec(v_as_3852_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3868_, lean_object* v_as_x27_3869_, lean_object* v_b_3870_, lean_object* v_a_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3869_, v_b_3870_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3884_, lean_object* v_as_x27_3885_, lean_object* v_b_3886_, lean_object* v_a_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3884_, v_as_x27_3885_, v_b_3886_, v_a_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec(v_as_x27_3885_);
lean_dec(v_as_3884_);
return v_res_3899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_3902_ = l_Lean_stringToMessageData(v___x_3901_);
return v___x_3902_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_3908_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3909_ = l_Lean_Name_append(v___x_3908_, v___x_3907_);
return v___x_3909_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_3912_ = l_Lean_stringToMessageData(v___x_3911_);
return v___x_3912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_3915_ = l_Lean_stringToMessageData(v___x_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_3916_, lean_object* v_rhs_3917_, lean_object* v_proof_3918_, uint8_t v_isHEq_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_st_ref_get(v_a_3920_);
lean_inc_ref(v_lhs_3916_);
v___x_3935_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3934_, v_lhs_3916_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
lean_dec(v___x_3934_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref(v___x_3935_);
v___x_3937_ = lean_st_ref_get(v_a_3920_);
lean_inc_ref(v_rhs_3917_);
v___x_3938_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3937_, v_rhs_3917_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
lean_dec(v___x_3937_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v_root_3940_; lean_object* v_root_3941_; uint8_t v___x_3942_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_a_3939_);
lean_dec_ref(v___x_3938_);
v_root_3940_ = lean_ctor_get(v_a_3936_, 2);
v_root_3941_ = lean_ctor_get(v_a_3939_, 2);
v___x_3942_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_3940_, v_root_3941_);
if (v___x_3942_ == 0)
{
lean_object* v_options_3943_; lean_object* v_inheritedTraceOptions_3944_; uint8_t v_hasTrace_3945_; uint8_t v___x_3946_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3983_; uint8_t v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; uint8_t v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; uint8_t v___y_4024_; lean_object* v___y_4029_; uint8_t v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4056_; uint8_t v___y_4057_; uint8_t v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4072_; uint8_t v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; uint8_t v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4088_; uint8_t v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; uint8_t v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4104_; uint8_t v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; uint8_t v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; uint8_t v___y_4118_; lean_object* v___y_4120_; lean_object* v_size_4121_; uint8_t v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v_size_4125_; uint8_t v_interpreted_4126_; uint8_t v_ctor_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; uint8_t v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4140_; uint8_t v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; uint8_t v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; uint8_t v___y_4154_; lean_object* v___y_4165_; uint8_t v_interpreted_4166_; lean_object* v___y_4167_; uint8_t v_valueInconsistency_4168_; uint8_t v_trueEqFalse_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4182_; lean_object* v___y_4183_; uint8_t v_valueInconsistency_4184_; uint8_t v_trueEqFalse_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; uint8_t v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; uint8_t v___y_4252_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; 
v_options_3943_ = lean_ctor_get(v_a_3928_, 2);
v_inheritedTraceOptions_3944_ = lean_ctor_get(v_a_3928_, 13);
v_hasTrace_3945_ = lean_ctor_get_uint8(v_options_3943_, sizeof(void*)*1);
v___x_3946_ = 1;
if (v_hasTrace_3945_ == 0)
{
v___y_4259_ = v_a_3920_;
v___y_4260_ = v_a_3921_;
v___y_4261_ = v_a_3922_;
v___y_4262_ = v_a_3923_;
v___y_4263_ = v_a_3924_;
v___y_4264_ = v_a_3925_;
v___y_4265_ = v_a_3926_;
v___y_4266_ = v_a_3927_;
v___y_4267_ = v_a_3928_;
v___y_4268_ = v_a_3929_;
goto v___jp_4258_;
}
else
{
lean_object* v___x_4294_; lean_object* v___y_4296_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4309_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3944_, v_options_3943_, v___x_4308_);
if (v___x_4309_ == 0)
{
v___y_4259_ = v_a_3920_;
v___y_4260_ = v_a_3921_;
v___y_4261_ = v_a_3922_;
v___y_4262_ = v_a_3923_;
v___y_4263_ = v_a_3924_;
v___y_4264_ = v_a_3925_;
v___y_4265_ = v_a_3926_;
v___y_4266_ = v_a_3927_;
v___y_4267_ = v_a_3928_;
v___y_4268_ = v_a_3929_;
goto v___jp_4258_;
}
else
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_Meta_Grind_updateLastTag(v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_dec_ref(v___x_4310_);
if (v_isHEq_3919_ == 0)
{
lean_object* v___x_4311_; 
lean_inc_ref(v_rhs_3917_);
lean_inc_ref(v_lhs_3916_);
v___x_4311_ = l_Lean_Meta_mkEq(v_lhs_3916_, v_rhs_3917_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
v___y_4296_ = v___x_4311_;
goto v___jp_4295_;
}
else
{
lean_object* v___x_4312_; 
lean_inc_ref(v_rhs_3917_);
lean_inc_ref(v_lhs_3916_);
v___x_4312_ = l_Lean_Meta_mkHEq(v_lhs_3916_, v_rhs_3917_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
v___y_4296_ = v___x_4312_;
goto v___jp_4295_;
}
}
else
{
lean_dec(v_a_3939_);
lean_dec(v_a_3936_);
lean_dec_ref(v_proof_3918_);
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
return v___x_4310_;
}
}
v___jp_4295_:
{
if (lean_obj_tag(v___y_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v_a_4297_ = lean_ctor_get(v___y_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref(v___y_4296_);
v___x_4298_ = l_Lean_MessageData_ofExpr(v_a_4297_);
v___x_4299_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4294_, v___x_4298_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_dec_ref(v___x_4299_);
v___y_4259_ = v_a_3920_;
v___y_4260_ = v_a_3921_;
v___y_4261_ = v_a_3922_;
v___y_4262_ = v_a_3923_;
v___y_4263_ = v_a_3924_;
v___y_4264_ = v_a_3925_;
v___y_4265_ = v_a_3926_;
v___y_4266_ = v_a_3927_;
v___y_4267_ = v_a_3928_;
v___y_4268_ = v_a_3929_;
goto v___jp_4258_;
}
else
{
lean_dec(v_a_3939_);
lean_dec(v_a_3936_);
lean_dec_ref(v_proof_3918_);
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
return v___x_4299_;
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec(v_a_3939_);
lean_dec(v_a_3936_);
lean_dec_ref(v_proof_3918_);
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
v_a_4300_ = lean_ctor_get(v___y_4296_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___y_4296_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___y_4296_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___y_4296_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
}
v___jp_3947_:
{
lean_object* v_options_3958_; uint8_t v_hasTrace_3959_; 
v_options_3958_ = lean_ctor_get(v___y_3956_, 2);
v_hasTrace_3959_ = lean_ctor_get_uint8(v_options_3958_, sizeof(void*)*1);
if (v_hasTrace_3959_ == 0)
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Lean_Meta_Grind_checkInvariants(v___x_3942_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
return v___x_3960_;
}
else
{
lean_object* v_inheritedTraceOptions_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v_inheritedTraceOptions_3961_ = lean_ctor_get(v___y_3956_, 13);
v___x_3962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3964_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3961_, v_options_3958_, v___x_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Lean_Meta_Grind_checkInvariants(v___x_3942_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
return v___x_3965_;
}
else
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Meta_Grind_updateLastTag(v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
lean_dec_ref(v___x_3966_);
v___x_3967_ = lean_st_ref_get(v___y_3948_);
v___x_3968_ = l_Lean_Meta_Grind_Goal_ppState(v___x_3967_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___x_3967_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref(v___x_3968_);
v___x_3970_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_3971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
lean_ctor_set(v___x_3971_, 1, v_a_3969_);
v___x_3972_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_3962_, v___x_3971_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v___x_3973_; 
lean_dec_ref(v___x_3972_);
v___x_3973_ = l_Lean_Meta_Grind_checkInvariants(v___x_3942_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
return v___x_3973_;
}
else
{
return v___x_3972_;
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
v_a_3974_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3968_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3968_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
else
{
return v___x_3966_;
}
}
}
}
v___jp_3982_:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3986_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; uint8_t v___x_3998_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref(v___x_3996_);
v___x_3998_ = lean_unbox(v_a_3997_);
lean_dec(v_a_3997_);
if (v___x_3998_ == 0)
{
if (v___y_3984_ == 0)
{
lean_dec_ref(v___y_3985_);
lean_dec_ref(v___y_3983_);
v___y_3948_ = v___y_3986_;
v___y_3949_ = v___y_3987_;
v___y_3950_ = v___y_3988_;
v___y_3951_ = v___y_3989_;
v___y_3952_ = v___y_3990_;
v___y_3953_ = v___y_3991_;
v___y_3954_ = v___y_3992_;
v___y_3955_ = v___y_3993_;
v___y_3956_ = v___y_3994_;
v___y_3957_ = v___y_3995_;
goto v___jp_3947_;
}
else
{
lean_object* v_self_3999_; lean_object* v_self_4000_; lean_object* v___x_4001_; 
v_self_3999_ = lean_ctor_get(v___y_3983_, 0);
lean_inc_ref(v_self_3999_);
lean_dec_ref(v___y_3983_);
v_self_4000_ = lean_ctor_get(v___y_3985_, 0);
lean_inc_ref(v_self_4000_);
lean_dec_ref(v___y_3985_);
v___x_4001_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_3999_, v_self_4000_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_dec_ref(v___x_4001_);
v___y_3948_ = v___y_3986_;
v___y_3949_ = v___y_3987_;
v___y_3950_ = v___y_3988_;
v___y_3951_ = v___y_3989_;
v___y_3952_ = v___y_3990_;
v___y_3953_ = v___y_3991_;
v___y_3954_ = v___y_3992_;
v___y_3955_ = v___y_3993_;
v___y_3956_ = v___y_3994_;
v___y_3957_ = v___y_3995_;
goto v___jp_3947_;
}
else
{
return v___x_4001_;
}
}
}
else
{
lean_dec_ref(v___y_3985_);
lean_dec_ref(v___y_3983_);
v___y_3948_ = v___y_3986_;
v___y_3949_ = v___y_3987_;
v___y_3950_ = v___y_3988_;
v___y_3951_ = v___y_3989_;
v___y_3952_ = v___y_3990_;
v___y_3953_ = v___y_3991_;
v___y_3954_ = v___y_3992_;
v___y_3955_ = v___y_3993_;
v___y_3956_ = v___y_3994_;
v___y_3957_ = v___y_3995_;
goto v___jp_3947_;
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v___y_3985_);
lean_dec_ref(v___y_3983_);
v_a_4002_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3996_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3996_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
v___jp_4010_:
{
if (v___y_4024_ == 0)
{
v___y_3983_ = v___y_4012_;
v___y_3984_ = v___y_4020_;
v___y_3985_ = v___y_4017_;
v___y_3986_ = v___y_4013_;
v___y_3987_ = v___y_4022_;
v___y_3988_ = v___y_4021_;
v___y_3989_ = v___y_4015_;
v___y_3990_ = v___y_4019_;
v___y_3991_ = v___y_4011_;
v___y_3992_ = v___y_4016_;
v___y_3993_ = v___y_4018_;
v___y_3994_ = v___y_4014_;
v___y_3995_ = v___y_4023_;
goto v___jp_3982_;
}
else
{
lean_object* v_self_4025_; lean_object* v_self_4026_; lean_object* v___x_4027_; 
v_self_4025_ = lean_ctor_get(v___y_4012_, 0);
v_self_4026_ = lean_ctor_get(v___y_4017_, 0);
lean_inc_ref(v_self_4026_);
lean_inc_ref(v_self_4025_);
v___x_4027_ = l_Lean_Meta_Grind_propagateCtor(v_self_4025_, v_self_4026_, v___y_4013_, v___y_4022_, v___y_4021_, v___y_4015_, v___y_4019_, v___y_4011_, v___y_4016_, v___y_4018_, v___y_4014_, v___y_4023_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_dec_ref(v___x_4027_);
v___y_3983_ = v___y_4012_;
v___y_3984_ = v___y_4020_;
v___y_3985_ = v___y_4017_;
v___y_3986_ = v___y_4013_;
v___y_3987_ = v___y_4022_;
v___y_3988_ = v___y_4021_;
v___y_3989_ = v___y_4015_;
v___y_3990_ = v___y_4019_;
v___y_3991_ = v___y_4011_;
v___y_3992_ = v___y_4016_;
v___y_3993_ = v___y_4018_;
v___y_3994_ = v___y_4014_;
v___y_3995_ = v___y_4023_;
goto v___jp_3982_;
}
else
{
lean_dec_ref(v___y_4017_);
lean_dec_ref(v___y_4012_);
return v___x_4027_;
}
}
}
v___jp_4028_:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4032_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; uint8_t v___x_4044_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref(v___x_4042_);
v___x_4044_ = lean_unbox(v_a_4043_);
lean_dec(v_a_4043_);
if (v___x_4044_ == 0)
{
uint8_t v_ctor_4045_; 
v_ctor_4045_ = lean_ctor_get_uint8(v___y_4029_, sizeof(void*)*12 + 2);
if (v_ctor_4045_ == 0)
{
v___y_4011_ = v___y_4037_;
v___y_4012_ = v___y_4029_;
v___y_4013_ = v___y_4032_;
v___y_4014_ = v___y_4040_;
v___y_4015_ = v___y_4035_;
v___y_4016_ = v___y_4038_;
v___y_4017_ = v___y_4031_;
v___y_4018_ = v___y_4039_;
v___y_4019_ = v___y_4036_;
v___y_4020_ = v___y_4030_;
v___y_4021_ = v___y_4034_;
v___y_4022_ = v___y_4033_;
v___y_4023_ = v___y_4041_;
v___y_4024_ = v___x_3942_;
goto v___jp_4010_;
}
else
{
uint8_t v_ctor_4046_; 
v_ctor_4046_ = lean_ctor_get_uint8(v___y_4031_, sizeof(void*)*12 + 2);
v___y_4011_ = v___y_4037_;
v___y_4012_ = v___y_4029_;
v___y_4013_ = v___y_4032_;
v___y_4014_ = v___y_4040_;
v___y_4015_ = v___y_4035_;
v___y_4016_ = v___y_4038_;
v___y_4017_ = v___y_4031_;
v___y_4018_ = v___y_4039_;
v___y_4019_ = v___y_4036_;
v___y_4020_ = v___y_4030_;
v___y_4021_ = v___y_4034_;
v___y_4022_ = v___y_4033_;
v___y_4023_ = v___y_4041_;
v___y_4024_ = v_ctor_4046_;
goto v___jp_4010_;
}
}
else
{
v___y_3983_ = v___y_4029_;
v___y_3984_ = v___y_4030_;
v___y_3985_ = v___y_4031_;
v___y_3986_ = v___y_4032_;
v___y_3987_ = v___y_4033_;
v___y_3988_ = v___y_4034_;
v___y_3989_ = v___y_4035_;
v___y_3990_ = v___y_4036_;
v___y_3991_ = v___y_4037_;
v___y_3992_ = v___y_4038_;
v___y_3993_ = v___y_4039_;
v___y_3994_ = v___y_4040_;
v___y_3995_ = v___y_4041_;
goto v___jp_3982_;
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec_ref(v___y_4031_);
lean_dec_ref(v___y_4029_);
v_a_4047_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4042_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4042_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
v___jp_4055_:
{
if (v___y_4058_ == 0)
{
v___y_4029_ = v___y_4056_;
v___y_4030_ = v___y_4057_;
v___y_4031_ = v___y_4059_;
v___y_4032_ = v___y_4060_;
v___y_4033_ = v___y_4061_;
v___y_4034_ = v___y_4062_;
v___y_4035_ = v___y_4063_;
v___y_4036_ = v___y_4064_;
v___y_4037_ = v___y_4065_;
v___y_4038_ = v___y_4066_;
v___y_4039_ = v___y_4067_;
v___y_4040_ = v___y_4068_;
v___y_4041_ = v___y_4069_;
goto v___jp_4028_;
}
else
{
lean_object* v___x_4070_; 
v___x_4070_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_dec_ref(v___x_4070_);
v___y_4029_ = v___y_4056_;
v___y_4030_ = v___y_4057_;
v___y_4031_ = v___y_4059_;
v___y_4032_ = v___y_4060_;
v___y_4033_ = v___y_4061_;
v___y_4034_ = v___y_4062_;
v___y_4035_ = v___y_4063_;
v___y_4036_ = v___y_4064_;
v___y_4037_ = v___y_4065_;
v___y_4038_ = v___y_4066_;
v___y_4039_ = v___y_4067_;
v___y_4040_ = v___y_4068_;
v___y_4041_ = v___y_4069_;
goto v___jp_4028_;
}
else
{
lean_dec_ref(v___y_4059_);
lean_dec_ref(v___y_4056_);
return v___x_4070_;
}
}
}
v___jp_4071_:
{
lean_object* v___x_4086_; 
lean_inc_ref(v___y_4072_);
lean_inc_ref(v___y_4075_);
v___x_4086_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3918_, v_isHEq_3919_, v_rhs_3917_, v_lhs_3916_, v_a_3939_, v_a_3936_, v___y_4075_, v___y_4072_, v___x_3946_, v___y_4084_, v___y_4085_, v___y_4081_, v___y_4079_, v___y_4080_, v___y_4074_, v___y_4076_, v___y_4077_, v___y_4083_, v___y_4082_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_dec_ref(v___x_4086_);
v___y_4056_ = v___y_4072_;
v___y_4057_ = v___y_4078_;
v___y_4058_ = v___y_4073_;
v___y_4059_ = v___y_4075_;
v___y_4060_ = v___y_4084_;
v___y_4061_ = v___y_4085_;
v___y_4062_ = v___y_4081_;
v___y_4063_ = v___y_4079_;
v___y_4064_ = v___y_4080_;
v___y_4065_ = v___y_4074_;
v___y_4066_ = v___y_4076_;
v___y_4067_ = v___y_4077_;
v___y_4068_ = v___y_4083_;
v___y_4069_ = v___y_4082_;
goto v___jp_4055_;
}
else
{
lean_dec_ref(v___y_4075_);
lean_dec_ref(v___y_4072_);
return v___x_4086_;
}
}
v___jp_4087_:
{
lean_object* v___x_4102_; 
lean_inc_ref(v___y_4091_);
lean_inc_ref(v___y_4088_);
v___x_4102_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3918_, v_isHEq_3919_, v_lhs_3916_, v_rhs_3917_, v_a_3936_, v_a_3939_, v___y_4088_, v___y_4091_, v___x_3942_, v___y_4100_, v___y_4101_, v___y_4097_, v___y_4095_, v___y_4096_, v___y_4090_, v___y_4092_, v___y_4093_, v___y_4099_, v___y_4098_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_dec_ref(v___x_4102_);
v___y_4056_ = v___y_4088_;
v___y_4057_ = v___y_4094_;
v___y_4058_ = v___y_4089_;
v___y_4059_ = v___y_4091_;
v___y_4060_ = v___y_4100_;
v___y_4061_ = v___y_4101_;
v___y_4062_ = v___y_4097_;
v___y_4063_ = v___y_4095_;
v___y_4064_ = v___y_4096_;
v___y_4065_ = v___y_4090_;
v___y_4066_ = v___y_4092_;
v___y_4067_ = v___y_4093_;
v___y_4068_ = v___y_4099_;
v___y_4069_ = v___y_4098_;
goto v___jp_4055_;
}
else
{
lean_dec_ref(v___y_4091_);
lean_dec_ref(v___y_4088_);
return v___x_4102_;
}
}
v___jp_4103_:
{
if (v___y_4118_ == 0)
{
v___y_4088_ = v___y_4104_;
v___y_4089_ = v___y_4105_;
v___y_4090_ = v___y_4106_;
v___y_4091_ = v___y_4107_;
v___y_4092_ = v___y_4108_;
v___y_4093_ = v___y_4109_;
v___y_4094_ = v___y_4110_;
v___y_4095_ = v___y_4111_;
v___y_4096_ = v___y_4112_;
v___y_4097_ = v___y_4113_;
v___y_4098_ = v___y_4114_;
v___y_4099_ = v___y_4115_;
v___y_4100_ = v___y_4116_;
v___y_4101_ = v___y_4117_;
goto v___jp_4087_;
}
else
{
v___y_4072_ = v___y_4104_;
v___y_4073_ = v___y_4105_;
v___y_4074_ = v___y_4106_;
v___y_4075_ = v___y_4107_;
v___y_4076_ = v___y_4108_;
v___y_4077_ = v___y_4109_;
v___y_4078_ = v___y_4110_;
v___y_4079_ = v___y_4111_;
v___y_4080_ = v___y_4112_;
v___y_4081_ = v___y_4113_;
v___y_4082_ = v___y_4114_;
v___y_4083_ = v___y_4115_;
v___y_4084_ = v___y_4116_;
v___y_4085_ = v___y_4117_;
goto v___jp_4071_;
}
}
v___jp_4119_:
{
uint8_t v___x_4138_; 
v___x_4138_ = lean_nat_dec_lt(v_size_4125_, v_size_4121_);
lean_dec(v_size_4121_);
lean_dec(v_size_4125_);
if (v___x_4138_ == 0)
{
v___y_4104_ = v___y_4120_;
v___y_4105_ = v___y_4122_;
v___y_4106_ = v___y_4123_;
v___y_4107_ = v___y_4124_;
v___y_4108_ = v___y_4128_;
v___y_4109_ = v___y_4129_;
v___y_4110_ = v___y_4130_;
v___y_4111_ = v___y_4131_;
v___y_4112_ = v___y_4132_;
v___y_4113_ = v___y_4133_;
v___y_4114_ = v___y_4134_;
v___y_4115_ = v___y_4135_;
v___y_4116_ = v___y_4136_;
v___y_4117_ = v___y_4137_;
v___y_4118_ = v___x_3942_;
goto v___jp_4103_;
}
else
{
if (v_interpreted_4126_ == 0)
{
if (v___x_4138_ == 0)
{
v___y_4104_ = v___y_4120_;
v___y_4105_ = v___y_4122_;
v___y_4106_ = v___y_4123_;
v___y_4107_ = v___y_4124_;
v___y_4108_ = v___y_4128_;
v___y_4109_ = v___y_4129_;
v___y_4110_ = v___y_4130_;
v___y_4111_ = v___y_4131_;
v___y_4112_ = v___y_4132_;
v___y_4113_ = v___y_4133_;
v___y_4114_ = v___y_4134_;
v___y_4115_ = v___y_4135_;
v___y_4116_ = v___y_4136_;
v___y_4117_ = v___y_4137_;
v___y_4118_ = v___x_3942_;
goto v___jp_4103_;
}
else
{
if (v_ctor_4127_ == 0)
{
v___y_4104_ = v___y_4120_;
v___y_4105_ = v___y_4122_;
v___y_4106_ = v___y_4123_;
v___y_4107_ = v___y_4124_;
v___y_4108_ = v___y_4128_;
v___y_4109_ = v___y_4129_;
v___y_4110_ = v___y_4130_;
v___y_4111_ = v___y_4131_;
v___y_4112_ = v___y_4132_;
v___y_4113_ = v___y_4133_;
v___y_4114_ = v___y_4134_;
v___y_4115_ = v___y_4135_;
v___y_4116_ = v___y_4136_;
v___y_4117_ = v___y_4137_;
v___y_4118_ = v___x_4138_;
goto v___jp_4103_;
}
else
{
v___y_4088_ = v___y_4120_;
v___y_4089_ = v___y_4122_;
v___y_4090_ = v___y_4123_;
v___y_4091_ = v___y_4124_;
v___y_4092_ = v___y_4128_;
v___y_4093_ = v___y_4129_;
v___y_4094_ = v___y_4130_;
v___y_4095_ = v___y_4131_;
v___y_4096_ = v___y_4132_;
v___y_4097_ = v___y_4133_;
v___y_4098_ = v___y_4134_;
v___y_4099_ = v___y_4135_;
v___y_4100_ = v___y_4136_;
v___y_4101_ = v___y_4137_;
goto v___jp_4087_;
}
}
}
else
{
v___y_4104_ = v___y_4120_;
v___y_4105_ = v___y_4122_;
v___y_4106_ = v___y_4123_;
v___y_4107_ = v___y_4124_;
v___y_4108_ = v___y_4128_;
v___y_4109_ = v___y_4129_;
v___y_4110_ = v___y_4130_;
v___y_4111_ = v___y_4131_;
v___y_4112_ = v___y_4132_;
v___y_4113_ = v___y_4133_;
v___y_4114_ = v___y_4134_;
v___y_4115_ = v___y_4135_;
v___y_4116_ = v___y_4136_;
v___y_4117_ = v___y_4137_;
v___y_4118_ = v___x_3942_;
goto v___jp_4103_;
}
}
}
v___jp_4139_:
{
if (v___y_4154_ == 0)
{
uint8_t v_ctor_4155_; 
v_ctor_4155_ = lean_ctor_get_uint8(v___y_4140_, sizeof(void*)*12 + 2);
if (v_ctor_4155_ == 0)
{
if (v___x_3942_ == 0)
{
lean_object* v_size_4156_; lean_object* v_size_4157_; uint8_t v_interpreted_4158_; uint8_t v_ctor_4159_; 
v_size_4156_ = lean_ctor_get(v___y_4140_, 6);
lean_inc(v_size_4156_);
v_size_4157_ = lean_ctor_get(v___y_4143_, 6);
lean_inc(v_size_4157_);
v_interpreted_4158_ = lean_ctor_get_uint8(v___y_4143_, sizeof(void*)*12 + 1);
v_ctor_4159_ = lean_ctor_get_uint8(v___y_4143_, sizeof(void*)*12 + 2);
v___y_4120_ = v___y_4140_;
v_size_4121_ = v_size_4156_;
v___y_4122_ = v___y_4141_;
v___y_4123_ = v___y_4142_;
v___y_4124_ = v___y_4143_;
v_size_4125_ = v_size_4157_;
v_interpreted_4126_ = v_interpreted_4158_;
v_ctor_4127_ = v_ctor_4159_;
v___y_4128_ = v___y_4144_;
v___y_4129_ = v___y_4145_;
v___y_4130_ = v___y_4146_;
v___y_4131_ = v___y_4147_;
v___y_4132_ = v___y_4148_;
v___y_4133_ = v___y_4149_;
v___y_4134_ = v___y_4150_;
v___y_4135_ = v___y_4151_;
v___y_4136_ = v___y_4152_;
v___y_4137_ = v___y_4153_;
goto v___jp_4119_;
}
else
{
v___y_4072_ = v___y_4140_;
v___y_4073_ = v___y_4141_;
v___y_4074_ = v___y_4142_;
v___y_4075_ = v___y_4143_;
v___y_4076_ = v___y_4144_;
v___y_4077_ = v___y_4145_;
v___y_4078_ = v___y_4146_;
v___y_4079_ = v___y_4147_;
v___y_4080_ = v___y_4148_;
v___y_4081_ = v___y_4149_;
v___y_4082_ = v___y_4150_;
v___y_4083_ = v___y_4151_;
v___y_4084_ = v___y_4152_;
v___y_4085_ = v___y_4153_;
goto v___jp_4071_;
}
}
else
{
uint8_t v_ctor_4160_; 
v_ctor_4160_ = lean_ctor_get_uint8(v___y_4143_, sizeof(void*)*12 + 2);
if (v_ctor_4160_ == 0)
{
v___y_4072_ = v___y_4140_;
v___y_4073_ = v___y_4141_;
v___y_4074_ = v___y_4142_;
v___y_4075_ = v___y_4143_;
v___y_4076_ = v___y_4144_;
v___y_4077_ = v___y_4145_;
v___y_4078_ = v___y_4146_;
v___y_4079_ = v___y_4147_;
v___y_4080_ = v___y_4148_;
v___y_4081_ = v___y_4149_;
v___y_4082_ = v___y_4150_;
v___y_4083_ = v___y_4151_;
v___y_4084_ = v___y_4152_;
v___y_4085_ = v___y_4153_;
goto v___jp_4071_;
}
else
{
lean_object* v_size_4161_; lean_object* v_size_4162_; uint8_t v_interpreted_4163_; 
v_size_4161_ = lean_ctor_get(v___y_4140_, 6);
lean_inc(v_size_4161_);
v_size_4162_ = lean_ctor_get(v___y_4143_, 6);
lean_inc(v_size_4162_);
v_interpreted_4163_ = lean_ctor_get_uint8(v___y_4143_, sizeof(void*)*12 + 1);
v___y_4120_ = v___y_4140_;
v_size_4121_ = v_size_4161_;
v___y_4122_ = v___y_4141_;
v___y_4123_ = v___y_4142_;
v___y_4124_ = v___y_4143_;
v_size_4125_ = v_size_4162_;
v_interpreted_4126_ = v_interpreted_4163_;
v_ctor_4127_ = v_ctor_4160_;
v___y_4128_ = v___y_4144_;
v___y_4129_ = v___y_4145_;
v___y_4130_ = v___y_4146_;
v___y_4131_ = v___y_4147_;
v___y_4132_ = v___y_4148_;
v___y_4133_ = v___y_4149_;
v___y_4134_ = v___y_4150_;
v___y_4135_ = v___y_4151_;
v___y_4136_ = v___y_4152_;
v___y_4137_ = v___y_4153_;
goto v___jp_4119_;
}
}
}
else
{
v___y_4072_ = v___y_4140_;
v___y_4073_ = v___y_4141_;
v___y_4074_ = v___y_4142_;
v___y_4075_ = v___y_4143_;
v___y_4076_ = v___y_4144_;
v___y_4077_ = v___y_4145_;
v___y_4078_ = v___y_4146_;
v___y_4079_ = v___y_4147_;
v___y_4080_ = v___y_4148_;
v___y_4081_ = v___y_4149_;
v___y_4082_ = v___y_4150_;
v___y_4083_ = v___y_4151_;
v___y_4084_ = v___y_4152_;
v___y_4085_ = v___y_4153_;
goto v___jp_4071_;
}
}
v___jp_4164_:
{
if (v_interpreted_4166_ == 0)
{
v___y_4140_ = v___y_4165_;
v___y_4141_ = v_trueEqFalse_4169_;
v___y_4142_ = v___y_4175_;
v___y_4143_ = v___y_4167_;
v___y_4144_ = v___y_4176_;
v___y_4145_ = v___y_4177_;
v___y_4146_ = v_valueInconsistency_4168_;
v___y_4147_ = v___y_4173_;
v___y_4148_ = v___y_4174_;
v___y_4149_ = v___y_4172_;
v___y_4150_ = v___y_4179_;
v___y_4151_ = v___y_4178_;
v___y_4152_ = v___y_4170_;
v___y_4153_ = v___y_4171_;
v___y_4154_ = v___x_3942_;
goto v___jp_4139_;
}
else
{
uint8_t v_interpreted_4180_; 
v_interpreted_4180_ = lean_ctor_get_uint8(v___y_4167_, sizeof(void*)*12 + 1);
if (v_interpreted_4180_ == 0)
{
v___y_4072_ = v___y_4165_;
v___y_4073_ = v_trueEqFalse_4169_;
v___y_4074_ = v___y_4175_;
v___y_4075_ = v___y_4167_;
v___y_4076_ = v___y_4176_;
v___y_4077_ = v___y_4177_;
v___y_4078_ = v_valueInconsistency_4168_;
v___y_4079_ = v___y_4173_;
v___y_4080_ = v___y_4174_;
v___y_4081_ = v___y_4172_;
v___y_4082_ = v___y_4179_;
v___y_4083_ = v___y_4178_;
v___y_4084_ = v___y_4170_;
v___y_4085_ = v___y_4171_;
goto v___jp_4071_;
}
else
{
v___y_4140_ = v___y_4165_;
v___y_4141_ = v_trueEqFalse_4169_;
v___y_4142_ = v___y_4175_;
v___y_4143_ = v___y_4167_;
v___y_4144_ = v___y_4176_;
v___y_4145_ = v___y_4177_;
v___y_4146_ = v_valueInconsistency_4168_;
v___y_4147_ = v___y_4173_;
v___y_4148_ = v___y_4174_;
v___y_4149_ = v___y_4172_;
v___y_4150_ = v___y_4179_;
v___y_4151_ = v___y_4178_;
v___y_4152_ = v___y_4170_;
v___y_4153_ = v___y_4171_;
v___y_4154_ = v___x_3942_;
goto v___jp_4139_;
}
}
}
v___jp_4181_:
{
uint8_t v_interpreted_4196_; 
v_interpreted_4196_ = lean_ctor_get_uint8(v___y_4182_, sizeof(void*)*12 + 1);
v___y_4165_ = v___y_4182_;
v_interpreted_4166_ = v_interpreted_4196_;
v___y_4167_ = v___y_4183_;
v_valueInconsistency_4168_ = v_valueInconsistency_4184_;
v_trueEqFalse_4169_ = v_trueEqFalse_4185_;
v___y_4170_ = v___y_4186_;
v___y_4171_ = v___y_4187_;
v___y_4172_ = v___y_4188_;
v___y_4173_ = v___y_4189_;
v___y_4174_ = v___y_4190_;
v___y_4175_ = v___y_4191_;
v___y_4176_ = v___y_4192_;
v___y_4177_ = v___y_4193_;
v___y_4178_ = v___y_4194_;
v___y_4179_ = v___y_4195_;
goto v___jp_4164_;
}
v___jp_4197_:
{
lean_object* v___x_4210_; 
v___x_4210_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4202_, v___y_4201_, v___y_4208_, v___y_4200_, v___y_4206_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_dec_ref(v___x_4210_);
v___y_4182_ = v___y_4198_;
v___y_4183_ = v___y_4203_;
v_valueInconsistency_4184_ = v___x_3942_;
v_trueEqFalse_4185_ = v___x_3946_;
v___y_4186_ = v___y_4202_;
v___y_4187_ = v___y_4204_;
v___y_4188_ = v___y_4209_;
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4199_;
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4201_;
v___y_4193_ = v___y_4208_;
v___y_4194_ = v___y_4200_;
v___y_4195_ = v___y_4206_;
goto v___jp_4181_;
}
else
{
lean_dec_ref(v___y_4203_);
lean_dec_ref(v___y_4198_);
lean_dec(v_a_3939_);
lean_dec(v_a_3936_);
lean_dec_ref(v_proof_3918_);
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
return v___x_4210_;
}
}
v___jp_4211_:
{
if (v___y_4215_ == 0)
{
lean_object* v_self_4225_; uint8_t v_interpreted_4226_; lean_object* v_self_4227_; lean_object* v___x_4228_; 
v_self_4225_ = lean_ctor_get(v___y_4212_, 0);
v_interpreted_4226_ = lean_ctor_get_uint8(v___y_4212_, sizeof(void*)*12 + 1);
v_self_4227_ = lean_ctor_get(v___y_4217_, 0);
lean_inc_ref(v_self_4227_);
lean_inc_ref(v_self_4225_);
v___x_4228_ = l_Lean_Meta_Grind_hasSameType(v_self_4225_, v_self_4227_, v___y_4216_, v___y_4223_, v___y_4214_, v___y_4221_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; uint8_t v___x_4230_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4229_);
lean_dec_ref(v___x_4228_);
v___x_4230_ = lean_unbox(v_a_4229_);
lean_dec(v_a_4229_);
if (v___x_4230_ == 0)
{
v___y_4165_ = v___y_4212_;
v_interpreted_4166_ = v_interpreted_4226_;
v___y_4167_ = v___y_4217_;
v_valueInconsistency_4168_ = v___x_3942_;
v_trueEqFalse_4169_ = v___x_3942_;
v___y_4170_ = v___y_4218_;
v___y_4171_ = v___y_4219_;
v___y_4172_ = v___y_4224_;
v___y_4173_ = v___y_4220_;
v___y_4174_ = v___y_4213_;
v___y_4175_ = v___y_4222_;
v___y_4176_ = v___y_4216_;
v___y_4177_ = v___y_4223_;
v___y_4178_ = v___y_4214_;
v___y_4179_ = v___y_4221_;
goto v___jp_4164_;
}
else
{
v___y_4165_ = v___y_4212_;
v_interpreted_4166_ = v_interpreted_4226_;
v___y_4167_ = v___y_4217_;
v_valueInconsistency_4168_ = v___x_3946_;
v_trueEqFalse_4169_ = v___x_3942_;
v___y_4170_ = v___y_4218_;
v___y_4171_ = v___y_4219_;
v___y_4172_ = v___y_4224_;
v___y_4173_ = v___y_4220_;
v___y_4174_ = v___y_4213_;
v___y_4175_ = v___y_4222_;
v___y_4176_ = v___y_4216_;
v___y_4177_ = v___y_4223_;
v___y_4178_ = v___y_4214_;
v___y_4179_ = v___y_4221_;
goto v___jp_4164_;
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec_ref(v___y_4217_);
lean_dec_ref(v___y_4212_);
lean_dec(v_a_3939_);
lean_dec(v_a_3936_);
lean_dec_ref(v_proof_3918_);
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
v_a_4231_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4228_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4228_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
v___y_4182_ = v___y_4212_;
v___y_4183_ = v___y_4217_;
v_valueInconsistency_4184_ = v___x_3946_;
v_trueEqFalse_4185_ = v___x_3942_;
v___y_4186_ = v___y_4218_;
v___y_4187_ = v___y_4219_;
v___y_4188_ = v___y_4224_;
v___y_4189_ = v___y_4220_;
v___y_4190_ = v___y_4213_;
v___y_4191_ = v___y_4222_;
v___y_4192_ = v___y_4216_;
v___y_4193_ = v___y_4223_;
v___y_4194_ = v___y_4214_;
v___y_4195_ = v___y_4221_;
goto v___jp_4181_;
}
}
v___jp_4239_:
{
if (v___y_4252_ == 0)
{
v___y_4182_ = v___y_4240_;
v___y_4183_ = v___y_4245_;
v_valueInconsistency_4184_ = v___x_3942_;
v_trueEqFalse_4185_ = v___x_3942_;
v___y_4186_ = v___y_4244_;
v___y_4187_ = v___y_4246_;
v___y_4188_ = v___y_4251_;
v___y_4189_ = v___y_4247_;
v___y_4190_ = v___y_4241_;
v___y_4191_ = v___y_4249_;
v___y_4192_ = v___y_4243_;
v___y_4193_ = v___y_4250_;
v___y_4194_ = v___y_4242_;
v___y_4195_ = v___y_4248_;
goto v___jp_4181_;
}
else
{
uint8_t v___x_4253_; 
lean_inc_ref(v_root_3940_);
v___x_4253_ = l_Lean_Expr_isTrue(v_root_3940_);
if (v___x_4253_ == 0)
{
uint8_t v___x_4254_; 
lean_inc_ref(v_root_3941_);
v___x_4254_ = l_Lean_Expr_isTrue(v_root_3941_);
if (v___x_4254_ == 0)
{
if (v_isHEq_3919_ == 0)
{
uint8_t v_heqProofs_4255_; 
v_heqProofs_4255_ = lean_ctor_get_uint8(v___y_4240_, sizeof(void*)*12 + 4);
if (v_heqProofs_4255_ == 0)
{
uint8_t v_heqProofs_4256_; 
v_heqProofs_4256_ = lean_ctor_get_uint8(v___y_4245_, sizeof(void*)*12 + 4);
if (v_heqProofs_4256_ == 0)
{
uint8_t v_interpreted_4257_; 
v_interpreted_4257_ = lean_ctor_get_uint8(v___y_4240_, sizeof(void*)*12 + 1);
v___y_4165_ = v___y_4240_;
v_interpreted_4166_ = v_interpreted_4257_;
v___y_4167_ = v___y_4245_;
v_valueInconsistency_4168_ = v___x_3946_;
v_trueEqFalse_4169_ = v___x_3942_;
v___y_4170_ = v___y_4244_;
v___y_4171_ = v___y_4246_;
v___y_4172_ = v___y_4251_;
v___y_4173_ = v___y_4247_;
v___y_4174_ = v___y_4241_;
v___y_4175_ = v___y_4249_;
v___y_4176_ = v___y_4243_;
v___y_4177_ = v___y_4250_;
v___y_4178_ = v___y_4242_;
v___y_4179_ = v___y_4248_;
goto v___jp_4164_;
}
else
{
v___y_4212_ = v___y_4240_;
v___y_4213_ = v___y_4241_;
v___y_4214_ = v___y_4242_;
v___y_4215_ = v___x_4254_;
v___y_4216_ = v___y_4243_;
v___y_4217_ = v___y_4245_;
v___y_4218_ = v___y_4244_;
v___y_4219_ = v___y_4246_;
v___y_4220_ = v___y_4247_;
v___y_4221_ = v___y_4248_;
v___y_4222_ = v___y_4249_;
v___y_4223_ = v___y_4250_;
v___y_4224_ = v___y_4251_;
goto v___jp_4211_;
}
}
else
{
v___y_4212_ = v___y_4240_;
v___y_4213_ = v___y_4241_;
v___y_4214_ = v___y_4242_;
v___y_4215_ = v___x_4254_;
v___y_4216_ = v___y_4243_;
v___y_4217_ = v___y_4245_;
v___y_4218_ = v___y_4244_;
v___y_4219_ = v___y_4246_;
v___y_4220_ = v___y_4247_;
v___y_4221_ = v___y_4248_;
v___y_4222_ = v___y_4249_;
v___y_4223_ = v___y_4250_;
v___y_4224_ = v___y_4251_;
goto v___jp_4211_;
}
}
else
{
v___y_4212_ = v___y_4240_;
v___y_4213_ = v___y_4241_;
v___y_4214_ = v___y_4242_;
v___y_4215_ = v___x_4254_;
v___y_4216_ = v___y_4243_;
v___y_4217_ = v___y_4245_;
v___y_4218_ = v___y_4244_;
v___y_4219_ = v___y_4246_;
v___y_4220_ = v___y_4247_;
v___y_4221_ = v___y_4248_;
v___y_4222_ = v___y_4249_;
v___y_4223_ = v___y_4250_;
v___y_4224_ = v___y_4251_;
goto v___jp_4211_;
}
}
else
{
v___y_4198_ = v___y_4240_;
v___y_4199_ = v___y_4241_;
v___y_4200_ = v___y_4242_;
v___y_4201_ = v___y_4243_;
v___y_4202_ = v___y_4244_;
v___y_4203_ = v___y_4245_;
v___y_4204_ = v___y_4246_;
v___y_4205_ = v___y_4247_;
v___y_4206_ = v___y_4248_;
v___y_4207_ = v___y_4249_;
v___y_4208_ = v___y_4250_;
v___y_4209_ = v___y_4251_;
goto v___jp_4197_;
}
}
else
{
v___y_4198_ = v___y_4240_;
v___y_4199_ = v___y_4241_;
v___y_4200_ = v___y_4242_;
v___y_4201_ = v___y_4243_;
v___y_4202_ = v___y_4244_;
v___y_4203_ = v___y_4245_;
v___y_4204_ = v___y_4246_;
v___y_4205_ = v___y_4247_;
v___y_4206_ = v___y_4248_;
v___y_4207_ = v___y_4249_;
v___y_4208_ = v___y_4250_;
v___y_4209_ = v___y_4251_;
goto v___jp_4197_;
}
}
}
v___jp_4258_:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4269_ = lean_st_ref_get(v___y_4259_);
lean_inc_ref(v_root_3940_);
v___x_4270_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4269_, v_root_3940_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
lean_dec(v___x_4269_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc(v_a_4271_);
lean_dec_ref(v___x_4270_);
v___x_4272_ = lean_st_ref_get(v___y_4259_);
lean_inc_ref(v_root_3941_);
v___x_4273_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4272_, v_root_3941_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
lean_dec(v___x_4272_);
if (lean_obj_tag(v___x_4273_) == 0)
{
uint8_t v_interpreted_4274_; 
v_interpreted_4274_ = lean_ctor_get_uint8(v_a_4271_, sizeof(void*)*12 + 1);
if (v_interpreted_4274_ == 0)
{
lean_object* v_a_4275_; 
v_a_4275_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4275_);
lean_dec_ref(v___x_4273_);
v___y_4240_ = v_a_4271_;
v___y_4241_ = v___y_4263_;
v___y_4242_ = v___y_4267_;
v___y_4243_ = v___y_4265_;
v___y_4244_ = v___y_4259_;
v___y_4245_ = v_a_4275_;
v___y_4246_ = v___y_4260_;
v___y_4247_ = v___y_4262_;
v___y_4248_ = v___y_4268_;
v___y_4249_ = v___y_4264_;
v___y_4250_ = v___y_4266_;
v___y_4251_ = v___y_4261_;
v___y_4252_ = v___x_3942_;
goto v___jp_4239_;
}
else
{
lean_object* v_a_4276_; uint8_t v_interpreted_4277_; 
v_a_4276_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4276_);
lean_dec_ref(v___x_4273_);
v_interpreted_4277_ = lean_ctor_get_uint8(v_a_4276_, sizeof(void*)*12 + 1);
v___y_4240_ = v_a_4271_;
v___y_4241_ = v___y_4263_;
v___y_4242_ = v___y_4267_;
v___y_4243_ = v___y_4265_;
v___y_4244_ = v___y_4259_;
v___y_4245_ = v_a_4276_;
v___y_4246_ = v___y_4260_;
v___y_4247_ = v___y_4262_;
v___y_4248_ = v___y_4268_;
v___y_4249_ = v___y_4264_;
v___y_4250_ = v___y_4266_;
v___y_4251_ = v___y_4261_;
v___y_4252_ = v_interpreted_4277_;
goto v___jp_4239_;
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec(v_a_4271_);
lean_dec(v_a_3939_);
lean_dec(v_a_3936_);
lean_dec_ref(v_proof_3918_);
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
v_a_4278_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4273_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4273_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
lean_dec(v_a_3939_);
lean_dec(v_a_3936_);
lean_dec_ref(v_proof_3918_);
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
v_a_4286_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4270_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4270_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
}
}
else
{
lean_object* v_options_4313_; uint8_t v_hasTrace_4314_; 
lean_dec(v_a_3939_);
lean_dec(v_a_3936_);
lean_dec_ref(v_proof_3918_);
v_options_4313_ = lean_ctor_get(v_a_3928_, 2);
v_hasTrace_4314_ = lean_ctor_get_uint8(v_options_4313_, sizeof(void*)*1);
if (v_hasTrace_4314_ == 0)
{
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
goto v___jp_3931_;
}
else
{
lean_object* v_inheritedTraceOptions_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; 
v_inheritedTraceOptions_4315_ = lean_ctor_get(v_a_3928_, 13);
v___x_4316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4318_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4315_, v_options_4313_, v___x_4317_);
if (v___x_4318_ == 0)
{
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
goto v___jp_3931_;
}
else
{
lean_object* v___x_4319_; 
v___x_4319_ = l_Lean_Meta_Grind_updateLastTag(v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v___x_4320_; 
lean_dec_ref(v___x_4319_);
v___x_4320_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3916_, v_a_3920_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; lean_object* v___x_4322_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4321_);
lean_dec_ref(v___x_4320_);
v___x_4322_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3917_, v_a_3920_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref(v___x_4322_);
v___x_4324_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4325_, 0, v_a_4321_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
v___x_4326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4325_);
lean_ctor_set(v___x_4326_, 1, v_a_4323_);
v___x_4327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4328_, 0, v___x_4326_);
lean_ctor_set(v___x_4328_, 1, v___x_4327_);
v___x_4329_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4316_, v___x_4328_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_dec_ref(v___x_4329_);
goto v___jp_3931_;
}
else
{
return v___x_4329_;
}
}
else
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4337_; 
lean_dec(v_a_4321_);
v_a_4330_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4332_ = v___x_4322_;
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4322_);
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
lean_dec_ref(v_rhs_3917_);
v_a_4338_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4340_ = v___x_4320_;
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4320_);
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
else
{
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
return v___x_4319_;
}
}
}
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec(v_a_3936_);
lean_dec_ref(v_proof_3918_);
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
v_a_4346_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_3938_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_3938_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4361_; 
lean_dec_ref(v_proof_3918_);
lean_dec_ref(v_rhs_3917_);
lean_dec_ref(v_lhs_3916_);
v_a_4354_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4356_ = v___x_3935_;
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_3935_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4359_; 
if (v_isShared_4357_ == 0)
{
v___x_4359_ = v___x_4356_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
v___jp_3931_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = lean_box(0);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
return v___x_3933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4362_, lean_object* v_rhs_4363_, lean_object* v_proof_4364_, lean_object* v_isHEq_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_){
_start:
{
uint8_t v_isHEq_boxed_4377_; lean_object* v_res_4378_; 
v_isHEq_boxed_4377_ = lean_unbox(v_isHEq_4365_);
v_res_4378_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4362_, v_rhs_4363_, v_proof_4364_, v_isHEq_boxed_4377_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_);
lean_dec(v_a_4375_);
lean_dec_ref(v_a_4374_);
lean_dec(v_a_4373_);
lean_dec_ref(v_a_4372_);
lean_dec(v_a_4371_);
lean_dec_ref(v_a_4370_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
lean_dec(v_a_4367_);
lean_dec(v_a_4366_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4381_){
_start:
{
lean_object* v___x_4383_; lean_object* v_toGoalState_4384_; lean_object* v_mvarId_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4421_; 
v___x_4383_ = lean_st_ref_take(v_a_4381_);
v_toGoalState_4384_ = lean_ctor_get(v___x_4383_, 0);
v_mvarId_4385_ = lean_ctor_get(v___x_4383_, 1);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4387_ = v___x_4383_;
v_isShared_4388_ = v_isSharedCheck_4421_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_mvarId_4385_);
lean_inc(v_toGoalState_4384_);
lean_dec(v___x_4383_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4421_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v_nextDeclIdx_4389_; lean_object* v_enodeMap_4390_; lean_object* v_exprs_4391_; lean_object* v_parents_4392_; lean_object* v_congrTable_4393_; lean_object* v_appMap_4394_; lean_object* v_indicesFound_4395_; uint8_t v_inconsistent_4396_; lean_object* v_nextIdx_4397_; lean_object* v_newRawFacts_4398_; lean_object* v_facts_4399_; lean_object* v_extThms_4400_; lean_object* v_ematch_4401_; lean_object* v_inj_4402_; lean_object* v_split_4403_; lean_object* v_clean_4404_; lean_object* v_sstates_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4419_; 
v_nextDeclIdx_4389_ = lean_ctor_get(v_toGoalState_4384_, 0);
v_enodeMap_4390_ = lean_ctor_get(v_toGoalState_4384_, 1);
v_exprs_4391_ = lean_ctor_get(v_toGoalState_4384_, 2);
v_parents_4392_ = lean_ctor_get(v_toGoalState_4384_, 3);
v_congrTable_4393_ = lean_ctor_get(v_toGoalState_4384_, 4);
v_appMap_4394_ = lean_ctor_get(v_toGoalState_4384_, 5);
v_indicesFound_4395_ = lean_ctor_get(v_toGoalState_4384_, 6);
v_inconsistent_4396_ = lean_ctor_get_uint8(v_toGoalState_4384_, sizeof(void*)*17);
v_nextIdx_4397_ = lean_ctor_get(v_toGoalState_4384_, 8);
v_newRawFacts_4398_ = lean_ctor_get(v_toGoalState_4384_, 9);
v_facts_4399_ = lean_ctor_get(v_toGoalState_4384_, 10);
v_extThms_4400_ = lean_ctor_get(v_toGoalState_4384_, 11);
v_ematch_4401_ = lean_ctor_get(v_toGoalState_4384_, 12);
v_inj_4402_ = lean_ctor_get(v_toGoalState_4384_, 13);
v_split_4403_ = lean_ctor_get(v_toGoalState_4384_, 14);
v_clean_4404_ = lean_ctor_get(v_toGoalState_4384_, 15);
v_sstates_4405_ = lean_ctor_get(v_toGoalState_4384_, 16);
v_isSharedCheck_4419_ = !lean_is_exclusive(v_toGoalState_4384_);
if (v_isSharedCheck_4419_ == 0)
{
lean_object* v_unused_4420_; 
v_unused_4420_ = lean_ctor_get(v_toGoalState_4384_, 7);
lean_dec(v_unused_4420_);
v___x_4407_ = v_toGoalState_4384_;
v_isShared_4408_ = v_isSharedCheck_4419_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_sstates_4405_);
lean_inc(v_clean_4404_);
lean_inc(v_split_4403_);
lean_inc(v_inj_4402_);
lean_inc(v_ematch_4401_);
lean_inc(v_extThms_4400_);
lean_inc(v_facts_4399_);
lean_inc(v_newRawFacts_4398_);
lean_inc(v_nextIdx_4397_);
lean_inc(v_indicesFound_4395_);
lean_inc(v_appMap_4394_);
lean_inc(v_congrTable_4393_);
lean_inc(v_parents_4392_);
lean_inc(v_exprs_4391_);
lean_inc(v_enodeMap_4390_);
lean_inc(v_nextDeclIdx_4389_);
lean_dec(v_toGoalState_4384_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4419_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4409_; lean_object* v___x_4411_; 
v___x_4409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 7, v___x_4409_);
v___x_4411_ = v___x_4407_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_nextDeclIdx_4389_);
lean_ctor_set(v_reuseFailAlloc_4418_, 1, v_enodeMap_4390_);
lean_ctor_set(v_reuseFailAlloc_4418_, 2, v_exprs_4391_);
lean_ctor_set(v_reuseFailAlloc_4418_, 3, v_parents_4392_);
lean_ctor_set(v_reuseFailAlloc_4418_, 4, v_congrTable_4393_);
lean_ctor_set(v_reuseFailAlloc_4418_, 5, v_appMap_4394_);
lean_ctor_set(v_reuseFailAlloc_4418_, 6, v_indicesFound_4395_);
lean_ctor_set(v_reuseFailAlloc_4418_, 7, v___x_4409_);
lean_ctor_set(v_reuseFailAlloc_4418_, 8, v_nextIdx_4397_);
lean_ctor_set(v_reuseFailAlloc_4418_, 9, v_newRawFacts_4398_);
lean_ctor_set(v_reuseFailAlloc_4418_, 10, v_facts_4399_);
lean_ctor_set(v_reuseFailAlloc_4418_, 11, v_extThms_4400_);
lean_ctor_set(v_reuseFailAlloc_4418_, 12, v_ematch_4401_);
lean_ctor_set(v_reuseFailAlloc_4418_, 13, v_inj_4402_);
lean_ctor_set(v_reuseFailAlloc_4418_, 14, v_split_4403_);
lean_ctor_set(v_reuseFailAlloc_4418_, 15, v_clean_4404_);
lean_ctor_set(v_reuseFailAlloc_4418_, 16, v_sstates_4405_);
lean_ctor_set_uint8(v_reuseFailAlloc_4418_, sizeof(void*)*17, v_inconsistent_4396_);
v___x_4411_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4413_; 
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 0, v___x_4411_);
v___x_4413_ = v___x_4387_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4411_);
lean_ctor_set(v_reuseFailAlloc_4417_, 1, v_mvarId_4385_);
v___x_4413_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4414_ = lean_st_ref_set(v_a_4381_, v___x_4413_);
v___x_4415_ = lean_box(0);
v___x_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
return v___x_4416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4422_, lean_object* v_a_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4422_);
lean_dec(v_a_4422_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4425_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_);
lean_dec(v_a_4446_);
lean_dec_ref(v_a_4445_);
lean_dec(v_a_4444_);
lean_dec_ref(v_a_4443_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
lean_dec(v_a_4440_);
lean_dec_ref(v_a_4439_);
lean_dec(v_a_4438_);
lean_dec(v_a_4437_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4449_){
_start:
{
lean_object* v___x_4451_; lean_object* v_toGoalState_4452_; lean_object* v_newFacts_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; uint8_t v___x_4457_; 
v___x_4451_ = lean_st_ref_get(v_a_4449_);
v_toGoalState_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc_ref(v_toGoalState_4452_);
lean_dec(v___x_4451_);
v_newFacts_4453_ = lean_ctor_get(v_toGoalState_4452_, 7);
lean_inc_ref(v_newFacts_4453_);
lean_dec_ref(v_toGoalState_4452_);
v___x_4454_ = lean_array_get_size(v_newFacts_4453_);
v___x_4455_ = lean_unsigned_to_nat(1u);
v___x_4456_ = lean_nat_sub(v___x_4454_, v___x_4455_);
v___x_4457_ = lean_nat_dec_lt(v___x_4456_, v___x_4454_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
lean_dec(v___x_4456_);
lean_dec_ref(v_newFacts_4453_);
v___x_4458_ = lean_box(0);
v___x_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4458_);
return v___x_4459_;
}
else
{
lean_object* v___x_4460_; lean_object* v_toGoalState_4461_; lean_object* v_mvarId_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4499_; 
v___x_4460_ = lean_st_ref_take(v_a_4449_);
v_toGoalState_4461_ = lean_ctor_get(v___x_4460_, 0);
v_mvarId_4462_ = lean_ctor_get(v___x_4460_, 1);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4464_ = v___x_4460_;
v_isShared_4465_ = v_isSharedCheck_4499_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_mvarId_4462_);
lean_inc(v_toGoalState_4461_);
lean_dec(v___x_4460_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4499_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v_nextDeclIdx_4466_; lean_object* v_enodeMap_4467_; lean_object* v_exprs_4468_; lean_object* v_parents_4469_; lean_object* v_congrTable_4470_; lean_object* v_appMap_4471_; lean_object* v_indicesFound_4472_; lean_object* v_newFacts_4473_; uint8_t v_inconsistent_4474_; lean_object* v_nextIdx_4475_; lean_object* v_newRawFacts_4476_; lean_object* v_facts_4477_; lean_object* v_extThms_4478_; lean_object* v_ematch_4479_; lean_object* v_inj_4480_; lean_object* v_split_4481_; lean_object* v_clean_4482_; lean_object* v_sstates_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4498_; 
v_nextDeclIdx_4466_ = lean_ctor_get(v_toGoalState_4461_, 0);
v_enodeMap_4467_ = lean_ctor_get(v_toGoalState_4461_, 1);
v_exprs_4468_ = lean_ctor_get(v_toGoalState_4461_, 2);
v_parents_4469_ = lean_ctor_get(v_toGoalState_4461_, 3);
v_congrTable_4470_ = lean_ctor_get(v_toGoalState_4461_, 4);
v_appMap_4471_ = lean_ctor_get(v_toGoalState_4461_, 5);
v_indicesFound_4472_ = lean_ctor_get(v_toGoalState_4461_, 6);
v_newFacts_4473_ = lean_ctor_get(v_toGoalState_4461_, 7);
v_inconsistent_4474_ = lean_ctor_get_uint8(v_toGoalState_4461_, sizeof(void*)*17);
v_nextIdx_4475_ = lean_ctor_get(v_toGoalState_4461_, 8);
v_newRawFacts_4476_ = lean_ctor_get(v_toGoalState_4461_, 9);
v_facts_4477_ = lean_ctor_get(v_toGoalState_4461_, 10);
v_extThms_4478_ = lean_ctor_get(v_toGoalState_4461_, 11);
v_ematch_4479_ = lean_ctor_get(v_toGoalState_4461_, 12);
v_inj_4480_ = lean_ctor_get(v_toGoalState_4461_, 13);
v_split_4481_ = lean_ctor_get(v_toGoalState_4461_, 14);
v_clean_4482_ = lean_ctor_get(v_toGoalState_4461_, 15);
v_sstates_4483_ = lean_ctor_get(v_toGoalState_4461_, 16);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_toGoalState_4461_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4485_ = v_toGoalState_4461_;
v_isShared_4486_ = v_isSharedCheck_4498_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_sstates_4483_);
lean_inc(v_clean_4482_);
lean_inc(v_split_4481_);
lean_inc(v_inj_4480_);
lean_inc(v_ematch_4479_);
lean_inc(v_extThms_4478_);
lean_inc(v_facts_4477_);
lean_inc(v_newRawFacts_4476_);
lean_inc(v_nextIdx_4475_);
lean_inc(v_newFacts_4473_);
lean_inc(v_indicesFound_4472_);
lean_inc(v_appMap_4471_);
lean_inc(v_congrTable_4470_);
lean_inc(v_parents_4469_);
lean_inc(v_exprs_4468_);
lean_inc(v_enodeMap_4467_);
lean_inc(v_nextDeclIdx_4466_);
lean_dec(v_toGoalState_4461_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4498_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
v___x_4487_ = lean_array_pop(v_newFacts_4473_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 7, v___x_4487_);
v___x_4489_ = v___x_4485_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4497_; 
v_reuseFailAlloc_4497_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_nextDeclIdx_4466_);
lean_ctor_set(v_reuseFailAlloc_4497_, 1, v_enodeMap_4467_);
lean_ctor_set(v_reuseFailAlloc_4497_, 2, v_exprs_4468_);
lean_ctor_set(v_reuseFailAlloc_4497_, 3, v_parents_4469_);
lean_ctor_set(v_reuseFailAlloc_4497_, 4, v_congrTable_4470_);
lean_ctor_set(v_reuseFailAlloc_4497_, 5, v_appMap_4471_);
lean_ctor_set(v_reuseFailAlloc_4497_, 6, v_indicesFound_4472_);
lean_ctor_set(v_reuseFailAlloc_4497_, 7, v___x_4487_);
lean_ctor_set(v_reuseFailAlloc_4497_, 8, v_nextIdx_4475_);
lean_ctor_set(v_reuseFailAlloc_4497_, 9, v_newRawFacts_4476_);
lean_ctor_set(v_reuseFailAlloc_4497_, 10, v_facts_4477_);
lean_ctor_set(v_reuseFailAlloc_4497_, 11, v_extThms_4478_);
lean_ctor_set(v_reuseFailAlloc_4497_, 12, v_ematch_4479_);
lean_ctor_set(v_reuseFailAlloc_4497_, 13, v_inj_4480_);
lean_ctor_set(v_reuseFailAlloc_4497_, 14, v_split_4481_);
lean_ctor_set(v_reuseFailAlloc_4497_, 15, v_clean_4482_);
lean_ctor_set(v_reuseFailAlloc_4497_, 16, v_sstates_4483_);
lean_ctor_set_uint8(v_reuseFailAlloc_4497_, sizeof(void*)*17, v_inconsistent_4474_);
v___x_4489_ = v_reuseFailAlloc_4497_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4491_; 
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 0, v___x_4489_);
v___x_4491_ = v___x_4464_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4489_);
lean_ctor_set(v_reuseFailAlloc_4496_, 1, v_mvarId_4462_);
v___x_4491_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4492_ = lean_st_ref_set(v_a_4449_, v___x_4491_);
v___x_4493_ = lean_array_fget(v_newFacts_4453_, v___x_4456_);
lean_dec(v___x_4456_);
lean_dec_ref(v_newFacts_4453_);
v___x_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
return v___x_4495_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4500_, lean_object* v_a_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4500_);
lean_dec(v_a_4500_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4503_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_);
lean_dec(v_a_4524_);
lean_dec_ref(v_a_4523_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec(v_a_4515_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4527_, lean_object* v_rhs_4528_, lean_object* v_proof_4529_, uint8_t v_isHEq_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4527_, v_rhs_4528_, v_proof_4529_, v_isHEq_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v___x_4543_; 
lean_dec_ref(v___x_4542_);
lean_inc(v_a_4540_);
lean_inc_ref(v_a_4539_);
lean_inc(v_a_4538_);
lean_inc_ref(v_a_4537_);
lean_inc(v_a_4536_);
lean_inc_ref(v_a_4535_);
lean_inc(v_a_4534_);
lean_inc_ref(v_a_4533_);
lean_inc(v_a_4532_);
lean_inc(v_a_4531_);
v___x_4543_ = lean_grind_process_new_facts(v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
return v___x_4543_;
}
else
{
return v___x_4542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4544_, lean_object* v_rhs_4545_, lean_object* v_proof_4546_, lean_object* v_isHEq_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_){
_start:
{
uint8_t v_isHEq_boxed_4559_; lean_object* v_res_4560_; 
v_isHEq_boxed_4559_ = lean_unbox(v_isHEq_4547_);
v_res_4560_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4544_, v_rhs_4545_, v_proof_4546_, v_isHEq_boxed_4559_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
lean_dec(v_a_4551_);
lean_dec_ref(v_a_4550_);
lean_dec(v_a_4549_);
lean_dec(v_a_4548_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4561_, lean_object* v_rhs_4562_, lean_object* v_proof_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
uint8_t v___x_4575_; lean_object* v___x_4576_; 
v___x_4575_ = 0;
v___x_4576_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4561_, v_rhs_4562_, v_proof_4563_, v___x_4575_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_);
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4577_, lean_object* v_rhs_4578_, lean_object* v_proof_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4577_, v_rhs_4578_, v_proof_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
lean_dec(v_a_4587_);
lean_dec_ref(v_a_4586_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
lean_dec(v_a_4583_);
lean_dec_ref(v_a_4582_);
lean_dec(v_a_4581_);
lean_dec(v_a_4580_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4592_, lean_object* v_rhs_4593_, lean_object* v_proof_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
uint8_t v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = 1;
v___x_4607_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4592_, v_rhs_4593_, v_proof_4594_, v___x_4606_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
return v___x_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4608_, lean_object* v_rhs_4609_, lean_object* v_proof_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4608_, v_rhs_4609_, v_proof_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec(v_a_4612_);
lean_dec(v_a_4611_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v___x_4626_; lean_object* v_toGoalState_4627_; lean_object* v_mvarId_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4664_; 
v___x_4626_ = lean_st_ref_take(v_a_4624_);
v_toGoalState_4627_ = lean_ctor_get(v___x_4626_, 0);
v_mvarId_4628_ = lean_ctor_get(v___x_4626_, 1);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4630_ = v___x_4626_;
v_isShared_4631_ = v_isSharedCheck_4664_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_mvarId_4628_);
lean_inc(v_toGoalState_4627_);
lean_dec(v___x_4626_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4664_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v_nextDeclIdx_4632_; lean_object* v_enodeMap_4633_; lean_object* v_exprs_4634_; lean_object* v_parents_4635_; lean_object* v_congrTable_4636_; lean_object* v_appMap_4637_; lean_object* v_indicesFound_4638_; lean_object* v_newFacts_4639_; uint8_t v_inconsistent_4640_; lean_object* v_nextIdx_4641_; lean_object* v_newRawFacts_4642_; lean_object* v_facts_4643_; lean_object* v_extThms_4644_; lean_object* v_ematch_4645_; lean_object* v_inj_4646_; lean_object* v_split_4647_; lean_object* v_clean_4648_; lean_object* v_sstates_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4663_; 
v_nextDeclIdx_4632_ = lean_ctor_get(v_toGoalState_4627_, 0);
v_enodeMap_4633_ = lean_ctor_get(v_toGoalState_4627_, 1);
v_exprs_4634_ = lean_ctor_get(v_toGoalState_4627_, 2);
v_parents_4635_ = lean_ctor_get(v_toGoalState_4627_, 3);
v_congrTable_4636_ = lean_ctor_get(v_toGoalState_4627_, 4);
v_appMap_4637_ = lean_ctor_get(v_toGoalState_4627_, 5);
v_indicesFound_4638_ = lean_ctor_get(v_toGoalState_4627_, 6);
v_newFacts_4639_ = lean_ctor_get(v_toGoalState_4627_, 7);
v_inconsistent_4640_ = lean_ctor_get_uint8(v_toGoalState_4627_, sizeof(void*)*17);
v_nextIdx_4641_ = lean_ctor_get(v_toGoalState_4627_, 8);
v_newRawFacts_4642_ = lean_ctor_get(v_toGoalState_4627_, 9);
v_facts_4643_ = lean_ctor_get(v_toGoalState_4627_, 10);
v_extThms_4644_ = lean_ctor_get(v_toGoalState_4627_, 11);
v_ematch_4645_ = lean_ctor_get(v_toGoalState_4627_, 12);
v_inj_4646_ = lean_ctor_get(v_toGoalState_4627_, 13);
v_split_4647_ = lean_ctor_get(v_toGoalState_4627_, 14);
v_clean_4648_ = lean_ctor_get(v_toGoalState_4627_, 15);
v_sstates_4649_ = lean_ctor_get(v_toGoalState_4627_, 16);
v_isSharedCheck_4663_ = !lean_is_exclusive(v_toGoalState_4627_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4651_ = v_toGoalState_4627_;
v_isShared_4652_ = v_isSharedCheck_4663_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_sstates_4649_);
lean_inc(v_clean_4648_);
lean_inc(v_split_4647_);
lean_inc(v_inj_4646_);
lean_inc(v_ematch_4645_);
lean_inc(v_extThms_4644_);
lean_inc(v_facts_4643_);
lean_inc(v_newRawFacts_4642_);
lean_inc(v_nextIdx_4641_);
lean_inc(v_newFacts_4639_);
lean_inc(v_indicesFound_4638_);
lean_inc(v_appMap_4637_);
lean_inc(v_congrTable_4636_);
lean_inc(v_parents_4635_);
lean_inc(v_exprs_4634_);
lean_inc(v_enodeMap_4633_);
lean_inc(v_nextDeclIdx_4632_);
lean_dec(v_toGoalState_4627_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4663_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4653_; lean_object* v___x_4655_; 
v___x_4653_ = l_Lean_PersistentArray_push___redArg(v_facts_4643_, v_fact_4623_);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 10, v___x_4653_);
v___x_4655_ = v___x_4651_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_nextDeclIdx_4632_);
lean_ctor_set(v_reuseFailAlloc_4662_, 1, v_enodeMap_4633_);
lean_ctor_set(v_reuseFailAlloc_4662_, 2, v_exprs_4634_);
lean_ctor_set(v_reuseFailAlloc_4662_, 3, v_parents_4635_);
lean_ctor_set(v_reuseFailAlloc_4662_, 4, v_congrTable_4636_);
lean_ctor_set(v_reuseFailAlloc_4662_, 5, v_appMap_4637_);
lean_ctor_set(v_reuseFailAlloc_4662_, 6, v_indicesFound_4638_);
lean_ctor_set(v_reuseFailAlloc_4662_, 7, v_newFacts_4639_);
lean_ctor_set(v_reuseFailAlloc_4662_, 8, v_nextIdx_4641_);
lean_ctor_set(v_reuseFailAlloc_4662_, 9, v_newRawFacts_4642_);
lean_ctor_set(v_reuseFailAlloc_4662_, 10, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4662_, 11, v_extThms_4644_);
lean_ctor_set(v_reuseFailAlloc_4662_, 12, v_ematch_4645_);
lean_ctor_set(v_reuseFailAlloc_4662_, 13, v_inj_4646_);
lean_ctor_set(v_reuseFailAlloc_4662_, 14, v_split_4647_);
lean_ctor_set(v_reuseFailAlloc_4662_, 15, v_clean_4648_);
lean_ctor_set(v_reuseFailAlloc_4662_, 16, v_sstates_4649_);
lean_ctor_set_uint8(v_reuseFailAlloc_4662_, sizeof(void*)*17, v_inconsistent_4640_);
v___x_4655_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
lean_object* v___x_4657_; 
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 0, v___x_4655_);
v___x_4657_ = v___x_4630_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4661_, 1, v_mvarId_4628_);
v___x_4657_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4658_ = lean_st_ref_set(v_a_4624_, v___x_4657_);
v___x_4659_ = lean_box(0);
v___x_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4659_);
return v___x_4660_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4665_, v_a_4666_);
lean_dec(v_a_4666_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_){
_start:
{
lean_object* v___x_4681_; 
v___x_4681_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4669_, v_a_4670_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v_res_4694_; 
v_res_4694_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec_ref(v_a_4685_);
lean_dec(v_a_4684_);
lean_dec(v_a_4683_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4695_, lean_object* v_rhs_4696_, lean_object* v_proof_4697_, lean_object* v_generation_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_){
_start:
{
lean_object* v___x_4710_; 
lean_inc_ref(v_rhs_4696_);
lean_inc_ref(v_lhs_4695_);
v___x_4710_ = l_Lean_Meta_mkEq(v_lhs_4695_, v_rhs_4696_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; lean_object* v___x_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4722_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc_n(v_a_4711_, 2);
lean_dec_ref(v___x_4710_);
v___x_4712_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4711_, v_a_4699_);
v_isSharedCheck_4722_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4722_ == 0)
{
lean_object* v_unused_4723_; 
v_unused_4723_ = lean_ctor_get(v___x_4712_, 0);
lean_dec(v_unused_4723_);
v___x_4714_ = v___x_4712_;
v_isShared_4715_ = v_isSharedCheck_4722_;
goto v_resetjp_4713_;
}
else
{
lean_dec(v___x_4712_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4722_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
lean_ctor_set_tag(v___x_4714_, 1);
lean_ctor_set(v___x_4714_, 0, v_a_4711_);
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4711_);
v___x_4717_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4718_; 
lean_inc(v_a_4708_);
lean_inc_ref(v_a_4707_);
lean_inc(v_a_4706_);
lean_inc_ref(v_a_4705_);
lean_inc(v_a_4704_);
lean_inc_ref(v_a_4703_);
lean_inc(v_a_4702_);
lean_inc_ref(v_a_4701_);
lean_inc(v_a_4700_);
lean_inc(v_a_4699_);
lean_inc_ref(v___x_4717_);
lean_inc(v_generation_4698_);
lean_inc_ref(v_lhs_4695_);
v___x_4718_ = lean_grind_internalize(v_lhs_4695_, v_generation_4698_, v___x_4717_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v___x_4719_; 
lean_dec_ref(v___x_4718_);
lean_inc(v_a_4708_);
lean_inc_ref(v_a_4707_);
lean_inc(v_a_4706_);
lean_inc_ref(v_a_4705_);
lean_inc(v_a_4704_);
lean_inc_ref(v_a_4703_);
lean_inc(v_a_4702_);
lean_inc_ref(v_a_4701_);
lean_inc(v_a_4700_);
lean_inc(v_a_4699_);
lean_inc_ref(v_rhs_4696_);
v___x_4719_ = lean_grind_internalize(v_rhs_4696_, v_generation_4698_, v___x_4717_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v___x_4720_; 
lean_dec_ref(v___x_4719_);
v___x_4720_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4695_, v_rhs_4696_, v_proof_4697_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
return v___x_4720_;
}
else
{
lean_dec_ref(v_proof_4697_);
lean_dec_ref(v_rhs_4696_);
lean_dec_ref(v_lhs_4695_);
return v___x_4719_;
}
}
else
{
lean_dec_ref(v___x_4717_);
lean_dec(v_generation_4698_);
lean_dec_ref(v_proof_4697_);
lean_dec_ref(v_rhs_4696_);
lean_dec_ref(v_lhs_4695_);
return v___x_4718_;
}
}
}
}
else
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4731_; 
lean_dec(v_generation_4698_);
lean_dec_ref(v_proof_4697_);
lean_dec_ref(v_rhs_4696_);
lean_dec_ref(v_lhs_4695_);
v_a_4724_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4726_ = v___x_4710_;
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___x_4710_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
if (v_isShared_4727_ == 0)
{
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4724_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4732_, lean_object* v_rhs_4733_, lean_object* v_proof_4734_, lean_object* v_generation_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4732_, v_rhs_4733_, v_proof_4734_, v_generation_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_);
lean_dec(v_a_4745_);
lean_dec_ref(v_a_4744_);
lean_dec(v_a_4743_);
lean_dec_ref(v_a_4742_);
lean_dec(v_a_4741_);
lean_dec_ref(v_a_4740_);
lean_dec(v_a_4739_);
lean_dec_ref(v_a_4738_);
lean_dec(v_a_4737_);
lean_dec(v_a_4736_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4748_, lean_object* v_generation_4749_, lean_object* v_p_4750_, uint8_t v_isNeg_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = lean_box(0);
lean_inc(v_a_4761_);
lean_inc_ref(v_a_4760_);
lean_inc(v_a_4759_);
lean_inc_ref(v_a_4758_);
lean_inc(v_a_4757_);
lean_inc_ref(v_a_4756_);
lean_inc(v_a_4755_);
lean_inc_ref(v_a_4754_);
lean_inc(v_a_4753_);
lean_inc(v_a_4752_);
lean_inc_ref(v_p_4750_);
v___x_4764_ = lean_grind_internalize(v_p_4750_, v_generation_4749_, v___x_4763_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_dec_ref(v___x_4764_);
if (v_isNeg_4751_ == 0)
{
lean_object* v___x_4765_; 
v___x_4765_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4756_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4767_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_a_4766_);
lean_dec_ref(v___x_4765_);
v___x_4767_ = l_Lean_Meta_mkEqTrue(v_proof_4748_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
if (lean_obj_tag(v___x_4767_) == 0)
{
lean_object* v_a_4768_; lean_object* v___x_4769_; 
v_a_4768_ = lean_ctor_get(v___x_4767_, 0);
lean_inc(v_a_4768_);
lean_dec_ref(v___x_4767_);
v___x_4769_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4750_, v_a_4766_, v_a_4768_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
return v___x_4769_;
}
else
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4777_; 
lean_dec(v_a_4766_);
lean_dec_ref(v_p_4750_);
v_a_4770_ = lean_ctor_get(v___x_4767_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4767_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4772_ = v___x_4767_;
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4767_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4770_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
lean_dec_ref(v_p_4750_);
lean_dec_ref(v_proof_4748_);
v_a_4778_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4765_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4765_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
else
{
lean_object* v___x_4786_; 
v___x_4786_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4756_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v_a_4787_; lean_object* v___x_4788_; 
v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
lean_inc(v_a_4787_);
lean_dec_ref(v___x_4786_);
v___x_4788_ = l_Lean_Meta_mkEqFalse(v_proof_4748_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4790_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
lean_inc(v_a_4789_);
lean_dec_ref(v___x_4788_);
v___x_4790_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4750_, v_a_4787_, v_a_4789_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
return v___x_4790_;
}
else
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4798_; 
lean_dec(v_a_4787_);
lean_dec_ref(v_p_4750_);
v_a_4791_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4793_ = v___x_4788_;
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4788_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4796_; 
if (v_isShared_4794_ == 0)
{
v___x_4796_ = v___x_4793_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
else
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
lean_dec_ref(v_p_4750_);
lean_dec_ref(v_proof_4748_);
v_a_4799_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4786_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4786_);
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
else
{
lean_dec_ref(v_p_4750_);
lean_dec_ref(v_proof_4748_);
return v___x_4764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4807_, lean_object* v_generation_4808_, lean_object* v_p_4809_, lean_object* v_isNeg_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_){
_start:
{
uint8_t v_isNeg_boxed_4822_; lean_object* v_res_4823_; 
v_isNeg_boxed_4822_ = lean_unbox(v_isNeg_4810_);
v_res_4823_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4807_, v_generation_4808_, v_p_4809_, v_isNeg_boxed_4822_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
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
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4824_, lean_object* v_generation_4825_, lean_object* v_p_4826_, lean_object* v_lhs_4827_, lean_object* v_rhs_4828_, uint8_t v_isNeg_4829_, uint8_t v_isHEq_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_){
_start:
{
if (v_isNeg_4829_ == 0)
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_inc_ref(v_p_4826_);
v___x_4842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4842_, 0, v_p_4826_);
lean_inc(v_a_4840_);
lean_inc_ref(v_a_4839_);
lean_inc(v_a_4838_);
lean_inc_ref(v_a_4837_);
lean_inc(v_a_4836_);
lean_inc_ref(v_a_4835_);
lean_inc(v_a_4834_);
lean_inc_ref(v_a_4833_);
lean_inc(v_a_4832_);
lean_inc(v_a_4831_);
lean_inc_ref(v___x_4842_);
lean_inc(v_generation_4825_);
lean_inc_ref(v_lhs_4827_);
v___x_4843_ = lean_grind_internalize(v_lhs_4827_, v_generation_4825_, v___x_4842_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v___x_4844_; 
lean_dec_ref(v___x_4843_);
lean_inc(v_a_4840_);
lean_inc_ref(v_a_4839_);
lean_inc(v_a_4838_);
lean_inc_ref(v_a_4837_);
lean_inc(v_a_4836_);
lean_inc_ref(v_a_4835_);
lean_inc(v_a_4834_);
lean_inc_ref(v_a_4833_);
lean_inc(v_a_4832_);
lean_inc(v_a_4831_);
lean_inc_ref(v_rhs_4828_);
v___x_4844_ = lean_grind_internalize(v_rhs_4828_, v_generation_4825_, v___x_4842_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
lean_dec_ref(v___x_4844_);
v___x_4845_ = lean_box(0);
v___x_4846_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4826_, v___x_4845_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v___x_4847_; 
lean_dec_ref(v___x_4846_);
v___x_4847_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4827_, v_rhs_4828_, v_proof_4824_, v_isHEq_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
return v___x_4847_;
}
else
{
lean_dec_ref(v_rhs_4828_);
lean_dec_ref(v_lhs_4827_);
lean_dec_ref(v_proof_4824_);
return v___x_4846_;
}
}
else
{
lean_dec_ref(v_rhs_4828_);
lean_dec_ref(v_lhs_4827_);
lean_dec_ref(v_p_4826_);
lean_dec_ref(v_proof_4824_);
return v___x_4844_;
}
}
else
{
lean_dec_ref(v___x_4842_);
lean_dec_ref(v_rhs_4828_);
lean_dec_ref(v_lhs_4827_);
lean_dec_ref(v_p_4826_);
lean_dec(v_generation_4825_);
lean_dec_ref(v_proof_4824_);
return v___x_4843_;
}
}
else
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
lean_dec_ref(v_rhs_4828_);
lean_dec_ref(v_lhs_4827_);
v___x_4848_ = lean_box(0);
lean_inc(v_a_4840_);
lean_inc_ref(v_a_4839_);
lean_inc(v_a_4838_);
lean_inc_ref(v_a_4837_);
lean_inc(v_a_4836_);
lean_inc_ref(v_a_4835_);
lean_inc(v_a_4834_);
lean_inc_ref(v_a_4833_);
lean_inc(v_a_4832_);
lean_inc(v_a_4831_);
lean_inc_ref(v_p_4826_);
v___x_4849_ = lean_grind_internalize(v_p_4826_, v_generation_4825_, v___x_4848_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v___x_4850_; 
lean_dec_ref(v___x_4849_);
v___x_4850_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4835_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4852_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_a_4851_);
lean_dec_ref(v___x_4850_);
v___x_4852_ = l_Lean_Meta_mkEqFalse(v_proof_4824_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; lean_object* v___x_4854_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc(v_a_4853_);
lean_dec_ref(v___x_4852_);
v___x_4854_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4826_, v_a_4851_, v_a_4853_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
return v___x_4854_;
}
else
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4862_; 
lean_dec(v_a_4851_);
lean_dec_ref(v_p_4826_);
v_a_4855_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4857_ = v___x_4852_;
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4852_);
v___x_4857_ = lean_box(0);
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
v_resetjp_4856_:
{
lean_object* v___x_4860_; 
if (v_isShared_4858_ == 0)
{
v___x_4860_ = v___x_4857_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4855_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
}
else
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
lean_dec_ref(v_p_4826_);
lean_dec_ref(v_proof_4824_);
v_a_4863_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4865_ = v___x_4850_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4850_);
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
lean_dec_ref(v_p_4826_);
lean_dec_ref(v_proof_4824_);
return v___x_4849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4871_ = _args[0];
lean_object* v_generation_4872_ = _args[1];
lean_object* v_p_4873_ = _args[2];
lean_object* v_lhs_4874_ = _args[3];
lean_object* v_rhs_4875_ = _args[4];
lean_object* v_isNeg_4876_ = _args[5];
lean_object* v_isHEq_4877_ = _args[6];
lean_object* v_a_4878_ = _args[7];
lean_object* v_a_4879_ = _args[8];
lean_object* v_a_4880_ = _args[9];
lean_object* v_a_4881_ = _args[10];
lean_object* v_a_4882_ = _args[11];
lean_object* v_a_4883_ = _args[12];
lean_object* v_a_4884_ = _args[13];
lean_object* v_a_4885_ = _args[14];
lean_object* v_a_4886_ = _args[15];
lean_object* v_a_4887_ = _args[16];
lean_object* v_a_4888_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4889_; uint8_t v_isHEq_boxed_4890_; lean_object* v_res_4891_; 
v_isNeg_boxed_4889_ = lean_unbox(v_isNeg_4876_);
v_isHEq_boxed_4890_ = lean_unbox(v_isHEq_4877_);
v_res_4891_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4871_, v_generation_4872_, v_p_4873_, v_lhs_4874_, v_rhs_4875_, v_isNeg_boxed_4889_, v_isHEq_boxed_4890_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
lean_dec(v_a_4887_);
lean_dec_ref(v_a_4886_);
lean_dec(v_a_4885_);
lean_dec_ref(v_a_4884_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_a_4881_);
lean_dec_ref(v_a_4880_);
lean_dec(v_a_4879_);
lean_dec(v_a_4878_);
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4895_, lean_object* v_generation_4896_, lean_object* v_p_4897_, uint8_t v_isNeg_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v___x_4910_; 
lean_inc_ref(v_p_4897_);
v___x_4910_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4897_, v_a_4906_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4912_; uint8_t v___x_4913_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref(v___x_4910_);
v___x_4912_ = l_Lean_Expr_cleanupAnnotations(v_a_4911_);
v___x_4913_ = l_Lean_Expr_isApp(v___x_4912_);
if (v___x_4913_ == 0)
{
lean_object* v___x_4914_; 
lean_dec_ref(v___x_4912_);
v___x_4914_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4895_, v_generation_4896_, v_p_4897_, v_isNeg_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
return v___x_4914_;
}
else
{
lean_object* v_arg_4915_; lean_object* v___x_4916_; uint8_t v___x_4917_; 
v_arg_4915_ = lean_ctor_get(v___x_4912_, 1);
lean_inc_ref(v_arg_4915_);
v___x_4916_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4912_);
v___x_4917_ = l_Lean_Expr_isApp(v___x_4916_);
if (v___x_4917_ == 0)
{
lean_object* v___x_4918_; 
lean_dec_ref(v___x_4916_);
lean_dec_ref(v_arg_4915_);
v___x_4918_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4895_, v_generation_4896_, v_p_4897_, v_isNeg_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
return v___x_4918_;
}
else
{
lean_object* v_arg_4919_; lean_object* v___x_4920_; uint8_t v___x_4921_; 
v_arg_4919_ = lean_ctor_get(v___x_4916_, 1);
lean_inc_ref(v_arg_4919_);
v___x_4920_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4916_);
v___x_4921_ = l_Lean_Expr_isApp(v___x_4920_);
if (v___x_4921_ == 0)
{
lean_object* v___x_4922_; 
lean_dec_ref(v___x_4920_);
lean_dec_ref(v_arg_4919_);
lean_dec_ref(v_arg_4915_);
v___x_4922_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4895_, v_generation_4896_, v_p_4897_, v_isNeg_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
return v___x_4922_;
}
else
{
lean_object* v_arg_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; uint8_t v___x_4926_; 
v_arg_4923_ = lean_ctor_get(v___x_4920_, 1);
lean_inc_ref(v_arg_4923_);
v___x_4924_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4920_);
v___x_4925_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_4926_ = l_Lean_Expr_isConstOf(v___x_4924_, v___x_4925_);
if (v___x_4926_ == 0)
{
uint8_t v___x_4927_; 
lean_dec_ref(v_arg_4919_);
v___x_4927_ = l_Lean_Expr_isApp(v___x_4924_);
if (v___x_4927_ == 0)
{
lean_object* v___x_4928_; 
lean_dec_ref(v___x_4924_);
lean_dec_ref(v_arg_4923_);
lean_dec_ref(v_arg_4915_);
v___x_4928_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4895_, v_generation_4896_, v_p_4897_, v_isNeg_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
return v___x_4928_;
}
else
{
lean_object* v___x_4929_; lean_object* v___x_4930_; uint8_t v___x_4931_; 
v___x_4929_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4924_);
v___x_4930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_4931_ = l_Lean_Expr_isConstOf(v___x_4929_, v___x_4930_);
lean_dec_ref(v___x_4929_);
if (v___x_4931_ == 0)
{
lean_object* v___x_4932_; 
lean_dec_ref(v_arg_4923_);
lean_dec_ref(v_arg_4915_);
v___x_4932_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4895_, v_generation_4896_, v_p_4897_, v_isNeg_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
return v___x_4932_;
}
else
{
lean_object* v___x_4933_; 
v___x_4933_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4895_, v_generation_4896_, v_p_4897_, v_arg_4923_, v_arg_4915_, v_isNeg_4898_, v___x_4931_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
return v___x_4933_;
}
}
}
else
{
uint8_t v___x_4934_; 
lean_dec_ref(v___x_4924_);
v___x_4934_ = l_Lean_Expr_isProp(v_arg_4923_);
lean_dec_ref(v_arg_4923_);
if (v___x_4934_ == 0)
{
lean_object* v___x_4935_; 
v___x_4935_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4895_, v_generation_4896_, v_p_4897_, v_arg_4919_, v_arg_4915_, v_isNeg_4898_, v___x_4934_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
return v___x_4935_;
}
else
{
lean_object* v___x_4936_; 
lean_dec_ref(v_arg_4919_);
lean_dec_ref(v_arg_4915_);
v___x_4936_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4895_, v_generation_4896_, v_p_4897_, v_isNeg_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
return v___x_4936_;
}
}
}
}
}
}
else
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4944_; 
lean_dec_ref(v_p_4897_);
lean_dec(v_generation_4896_);
lean_dec_ref(v_proof_4895_);
v_a_4937_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4939_ = v___x_4910_;
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4910_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_4945_, lean_object* v_generation_4946_, lean_object* v_p_4947_, lean_object* v_isNeg_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
uint8_t v_isNeg_boxed_4960_; lean_object* v_res_4961_; 
v_isNeg_boxed_4960_ = lean_unbox(v_isNeg_4948_);
v_res_4961_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4945_, v_generation_4946_, v_p_4947_, v_isNeg_boxed_4960_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
lean_dec(v_a_4952_);
lean_dec_ref(v_a_4951_);
lean_dec(v_a_4950_);
lean_dec(v_a_4949_);
return v_res_4961_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_4970_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4971_ = l_Lean_Name_append(v___x_4970_, v___x_4969_);
return v___x_4971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_4972_, lean_object* v_proof_4973_, lean_object* v_generation_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_){
_start:
{
lean_object* v___y_4987_; lean_object* v___y_4988_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_4995_; lean_object* v___y_4996_; lean_object* v___y_5000_; lean_object* v___y_5001_; lean_object* v___y_5002_; lean_object* v___y_5003_; lean_object* v___y_5004_; lean_object* v___y_5005_; lean_object* v___y_5006_; lean_object* v___y_5007_; lean_object* v___y_5008_; lean_object* v___y_5009_; lean_object* v___x_5017_; lean_object* v_options_5018_; uint8_t v_hasTrace_5019_; 
lean_inc_ref(v_fact_4972_);
v___x_5017_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4972_, v_a_4975_);
lean_dec_ref(v___x_5017_);
v_options_5018_ = lean_ctor_get(v_a_4983_, 2);
v_hasTrace_5019_ = lean_ctor_get_uint8(v_options_5018_, sizeof(void*)*1);
if (v_hasTrace_5019_ == 0)
{
v___y_5000_ = v_a_4975_;
v___y_5001_ = v_a_4976_;
v___y_5002_ = v_a_4977_;
v___y_5003_ = v_a_4978_;
v___y_5004_ = v_a_4979_;
v___y_5005_ = v_a_4980_;
v___y_5006_ = v_a_4981_;
v___y_5007_ = v_a_4982_;
v___y_5008_ = v_a_4983_;
v___y_5009_ = v_a_4984_;
goto v___jp_4999_;
}
else
{
lean_object* v_inheritedTraceOptions_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; uint8_t v___x_5023_; 
v_inheritedTraceOptions_5020_ = lean_ctor_get(v_a_4983_, 13);
v___x_5021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5022_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5023_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5020_, v_options_5018_, v___x_5022_);
if (v___x_5023_ == 0)
{
v___y_5000_ = v_a_4975_;
v___y_5001_ = v_a_4976_;
v___y_5002_ = v_a_4977_;
v___y_5003_ = v_a_4978_;
v___y_5004_ = v_a_4979_;
v___y_5005_ = v_a_4980_;
v___y_5006_ = v_a_4981_;
v___y_5007_ = v_a_4982_;
v___y_5008_ = v_a_4983_;
v___y_5009_ = v_a_4984_;
goto v___jp_4999_;
}
else
{
lean_object* v___x_5024_; 
v___x_5024_ = l_Lean_Meta_Grind_updateLastTag(v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_object* v___x_5025_; lean_object* v___x_5026_; 
lean_dec_ref(v___x_5024_);
lean_inc_ref(v_fact_4972_);
v___x_5025_ = l_Lean_MessageData_ofExpr(v_fact_4972_);
v___x_5026_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5021_, v___x_5025_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
if (lean_obj_tag(v___x_5026_) == 0)
{
lean_dec_ref(v___x_5026_);
v___y_5000_ = v_a_4975_;
v___y_5001_ = v_a_4976_;
v___y_5002_ = v_a_4977_;
v___y_5003_ = v_a_4978_;
v___y_5004_ = v_a_4979_;
v___y_5005_ = v_a_4980_;
v___y_5006_ = v_a_4981_;
v___y_5007_ = v_a_4982_;
v___y_5008_ = v_a_4983_;
v___y_5009_ = v_a_4984_;
goto v___jp_4999_;
}
else
{
lean_dec(v_generation_4974_);
lean_dec_ref(v_proof_4973_);
lean_dec_ref(v_fact_4972_);
return v___x_5026_;
}
}
else
{
lean_dec(v_generation_4974_);
lean_dec_ref(v_proof_4973_);
lean_dec_ref(v_fact_4972_);
return v___x_5024_;
}
}
}
v___jp_4986_:
{
uint8_t v___x_4997_; lean_object* v___x_4998_; 
v___x_4997_ = 0;
v___x_4998_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4973_, v_generation_4974_, v_fact_4972_, v___x_4997_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
return v___x_4998_;
}
v___jp_4999_:
{
lean_object* v___x_5010_; uint8_t v___x_5011_; 
lean_inc_ref(v_fact_4972_);
v___x_5010_ = l_Lean_Expr_cleanupAnnotations(v_fact_4972_);
v___x_5011_ = l_Lean_Expr_isApp(v___x_5010_);
if (v___x_5011_ == 0)
{
lean_dec_ref(v___x_5010_);
v___y_4987_ = v___y_5000_;
v___y_4988_ = v___y_5001_;
v___y_4989_ = v___y_5002_;
v___y_4990_ = v___y_5003_;
v___y_4991_ = v___y_5004_;
v___y_4992_ = v___y_5005_;
v___y_4993_ = v___y_5006_;
v___y_4994_ = v___y_5007_;
v___y_4995_ = v___y_5008_;
v___y_4996_ = v___y_5009_;
goto v___jp_4986_;
}
else
{
lean_object* v_arg_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; uint8_t v___x_5015_; 
v_arg_5012_ = lean_ctor_get(v___x_5010_, 1);
lean_inc_ref(v_arg_5012_);
v___x_5013_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5010_);
v___x_5014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5015_ = l_Lean_Expr_isConstOf(v___x_5013_, v___x_5014_);
lean_dec_ref(v___x_5013_);
if (v___x_5015_ == 0)
{
lean_dec_ref(v_arg_5012_);
v___y_4987_ = v___y_5000_;
v___y_4988_ = v___y_5001_;
v___y_4989_ = v___y_5002_;
v___y_4990_ = v___y_5003_;
v___y_4991_ = v___y_5004_;
v___y_4992_ = v___y_5005_;
v___y_4993_ = v___y_5006_;
v___y_4994_ = v___y_5007_;
v___y_4995_ = v___y_5008_;
v___y_4996_ = v___y_5009_;
goto v___jp_4986_;
}
else
{
lean_object* v___x_5016_; 
lean_dec_ref(v_fact_4972_);
v___x_5016_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4973_, v_generation_4974_, v_arg_5012_, v___x_5015_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
return v___x_5016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5027_, lean_object* v_proof_5028_, lean_object* v_generation_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5027_, v_proof_5028_, v_generation_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_);
lean_dec(v_a_5039_);
lean_dec_ref(v_a_5038_);
lean_dec(v_a_5037_);
lean_dec_ref(v_a_5036_);
lean_dec(v_a_5035_);
lean_dec_ref(v_a_5034_);
lean_dec(v_a_5033_);
lean_dec_ref(v_a_5032_);
lean_dec(v_a_5031_);
lean_dec(v_a_5030_);
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v___x_5056_; 
v___x_5056_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5045_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_object* v_a_5057_; uint8_t v___x_5058_; 
v_a_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_a_5057_);
lean_dec_ref(v___x_5056_);
v___x_5058_ = lean_unbox(v_a_5057_);
lean_dec(v_a_5057_);
if (v___x_5058_ == 0)
{
lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5059_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5060_ = l_Lean_Core_checkSystem(v___x_5059_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v___x_5061_; 
lean_dec_ref(v___x_5060_);
v___x_5061_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5045_);
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v_a_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5098_; 
v_a_5062_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5098_ == 0)
{
v___x_5064_ = v___x_5061_;
v_isShared_5065_ = v_isSharedCheck_5098_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_a_5062_);
lean_dec(v___x_5061_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5098_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
if (lean_obj_tag(v_a_5062_) == 1)
{
lean_object* v_val_5066_; 
lean_del_object(v___x_5064_);
v_val_5066_ = lean_ctor_get(v_a_5062_, 0);
lean_inc(v_val_5066_);
lean_dec_ref(v_a_5062_);
if (lean_obj_tag(v_val_5066_) == 0)
{
lean_object* v_lhs_5067_; lean_object* v_rhs_5068_; lean_object* v_proof_5069_; uint8_t v_isHEq_5070_; lean_object* v___x_5071_; 
v_lhs_5067_ = lean_ctor_get(v_val_5066_, 0);
lean_inc_ref(v_lhs_5067_);
v_rhs_5068_ = lean_ctor_get(v_val_5066_, 1);
lean_inc_ref(v_rhs_5068_);
v_proof_5069_ = lean_ctor_get(v_val_5066_, 2);
lean_inc_ref(v_proof_5069_);
v_isHEq_5070_ = lean_ctor_get_uint8(v_val_5066_, sizeof(void*)*3);
lean_dec_ref(v_val_5066_);
v___x_5071_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5067_, v_rhs_5068_, v_proof_5069_, v_isHEq_5070_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5071_) == 0)
{
lean_dec_ref(v___x_5071_);
goto _start;
}
else
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
v_a_5073_ = lean_ctor_get(v___x_5071_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5071_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5071_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
else
{
lean_object* v_prop_5081_; lean_object* v_proof_5082_; lean_object* v_generation_5083_; lean_object* v___x_5084_; 
v_prop_5081_ = lean_ctor_get(v_val_5066_, 0);
lean_inc_ref(v_prop_5081_);
v_proof_5082_ = lean_ctor_get(v_val_5066_, 1);
lean_inc_ref(v_proof_5082_);
v_generation_5083_ = lean_ctor_get(v_val_5066_, 2);
lean_inc(v_generation_5083_);
lean_dec_ref(v_val_5066_);
v___x_5084_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5081_, v_proof_5082_, v_generation_5083_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_dec_ref(v___x_5084_);
goto _start;
}
else
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
v_a_5086_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5084_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5084_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
}
else
{
lean_object* v___x_5094_; lean_object* v___x_5096_; 
lean_dec(v_a_5062_);
v___x_5094_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5065_ == 0)
{
lean_ctor_set(v___x_5064_, 0, v___x_5094_);
v___x_5096_ = v___x_5064_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5094_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
}
}
else
{
lean_object* v_a_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5106_; 
v_a_5099_ = lean_ctor_get(v___x_5061_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v___x_5061_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_5101_ = v___x_5061_;
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_a_5099_);
lean_dec(v___x_5061_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5104_; 
if (v_isShared_5102_ == 0)
{
v___x_5104_ = v___x_5101_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
return v___x_5104_;
}
}
}
}
else
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
v_a_5107_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_5060_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_5060_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_a_5107_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
}
else
{
lean_object* v___x_5115_; 
v___x_5115_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5045_);
if (lean_obj_tag(v___x_5115_) == 0)
{
lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5123_; 
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5123_ == 0)
{
lean_object* v_unused_5124_; 
v_unused_5124_ = lean_ctor_get(v___x_5115_, 0);
lean_dec(v_unused_5124_);
v___x_5117_ = v___x_5115_;
v_isShared_5118_ = v_isSharedCheck_5123_;
goto v_resetjp_5116_;
}
else
{
lean_dec(v___x_5115_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5123_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5119_; lean_object* v___x_5121_; 
v___x_5119_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5118_ == 0)
{
lean_ctor_set(v___x_5117_, 0, v___x_5119_);
v___x_5121_ = v___x_5117_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5119_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
v_a_5125_ = lean_ctor_get(v___x_5115_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5115_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5115_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
}
}
}
else
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5140_; 
v_a_5133_ = lean_ctor_get(v___x_5056_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5056_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5135_ = v___x_5056_;
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_5056_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5138_; 
if (v_isShared_5136_ == 0)
{
v___x_5138_ = v___x_5135_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
return v___x_5138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
lean_dec(v___y_5142_);
lean_dec(v___y_5141_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_){
_start:
{
lean_object* v___x_5164_; 
v___x_5164_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5153_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
lean_dec(v_a_5162_);
lean_dec_ref(v_a_5161_);
lean_dec(v_a_5160_);
lean_dec_ref(v_a_5159_);
lean_dec(v_a_5158_);
lean_dec_ref(v_a_5157_);
lean_dec(v_a_5156_);
lean_dec_ref(v_a_5155_);
lean_dec(v_a_5154_);
lean_dec(v_a_5153_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5178_; 
v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5167_ = v___x_5164_;
v_isShared_5168_ = v_isSharedCheck_5178_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5164_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5178_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v_fst_5169_; 
v_fst_5169_ = lean_ctor_get(v_a_5165_, 0);
lean_inc(v_fst_5169_);
lean_dec(v_a_5165_);
if (lean_obj_tag(v_fst_5169_) == 0)
{
lean_object* v___x_5170_; lean_object* v___x_5172_; 
v___x_5170_ = lean_box(0);
if (v_isShared_5168_ == 0)
{
lean_ctor_set(v___x_5167_, 0, v___x_5170_);
v___x_5172_ = v___x_5167_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5170_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
else
{
lean_object* v_val_5174_; lean_object* v___x_5176_; 
v_val_5174_ = lean_ctor_get(v_fst_5169_, 0);
lean_inc(v_val_5174_);
lean_dec_ref(v_fst_5169_);
if (v_isShared_5168_ == 0)
{
lean_ctor_set(v___x_5167_, 0, v_val_5174_);
v___x_5176_ = v___x_5167_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_val_5174_);
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
else
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5186_; 
v_a_5179_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5181_ = v___x_5164_;
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5164_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = lean_grind_process_new_facts(v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_, v_a_5196_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_b_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_){
_start:
{
lean_object* v___x_5211_; 
v___x_5211_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_b_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_){
_start:
{
lean_object* v_res_5224_; 
v_res_5224_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_b_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_);
lean_dec(v___y_5222_);
lean_dec_ref(v___y_5221_);
lean_dec(v___y_5220_);
lean_dec_ref(v___y_5219_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v_b_5212_);
return v_res_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5225_, lean_object* v_proof_5226_, lean_object* v_generation_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_){
_start:
{
uint8_t v___x_5239_; 
lean_inc_ref(v_fact_5225_);
v___x_5239_ = l_Lean_Expr_isTrue(v_fact_5225_);
if (v___x_5239_ == 0)
{
lean_object* v___x_5240_; 
v___x_5240_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5228_);
if (lean_obj_tag(v___x_5240_) == 0)
{
lean_object* v_a_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5252_; 
v_a_5241_ = lean_ctor_get(v___x_5240_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5240_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5243_ = v___x_5240_;
v_isShared_5244_ = v_isSharedCheck_5252_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_a_5241_);
lean_dec(v___x_5240_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5252_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
uint8_t v___x_5245_; 
v___x_5245_ = lean_unbox(v_a_5241_);
lean_dec(v_a_5241_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; lean_object* v___x_5247_; 
lean_del_object(v___x_5243_);
v___x_5246_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5228_);
lean_dec_ref(v___x_5246_);
v___x_5247_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5225_, v_proof_5226_, v_generation_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_, v_a_5236_, v_a_5237_);
return v___x_5247_;
}
else
{
lean_object* v___x_5248_; lean_object* v___x_5250_; 
lean_dec(v_generation_5227_);
lean_dec_ref(v_proof_5226_);
lean_dec_ref(v_fact_5225_);
v___x_5248_ = lean_box(0);
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 0, v___x_5248_);
v___x_5250_ = v___x_5243_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v___x_5248_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
}
else
{
lean_object* v_a_5253_; lean_object* v___x_5255_; uint8_t v_isShared_5256_; uint8_t v_isSharedCheck_5260_; 
lean_dec(v_generation_5227_);
lean_dec_ref(v_proof_5226_);
lean_dec_ref(v_fact_5225_);
v_a_5253_ = lean_ctor_get(v___x_5240_, 0);
v_isSharedCheck_5260_ = !lean_is_exclusive(v___x_5240_);
if (v_isSharedCheck_5260_ == 0)
{
v___x_5255_ = v___x_5240_;
v_isShared_5256_ = v_isSharedCheck_5260_;
goto v_resetjp_5254_;
}
else
{
lean_inc(v_a_5253_);
lean_dec(v___x_5240_);
v___x_5255_ = lean_box(0);
v_isShared_5256_ = v_isSharedCheck_5260_;
goto v_resetjp_5254_;
}
v_resetjp_5254_:
{
lean_object* v___x_5258_; 
if (v_isShared_5256_ == 0)
{
v___x_5258_ = v___x_5255_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v_a_5253_);
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
lean_object* v___x_5261_; lean_object* v___x_5262_; 
lean_dec(v_generation_5227_);
lean_dec_ref(v_proof_5226_);
lean_dec_ref(v_fact_5225_);
v___x_5261_ = lean_box(0);
v___x_5262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5262_, 0, v___x_5261_);
return v___x_5262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5263_, lean_object* v_proof_5264_, lean_object* v_generation_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l_Lean_Meta_Grind_add(v_fact_5263_, v_proof_5264_, v_generation_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_);
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
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5278_, lean_object* v_generation_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_){
_start:
{
lean_object* v___x_5291_; 
lean_inc(v_fvarId_5278_);
v___x_5291_ = l_Lean_FVarId_getType___redArg(v_fvarId_5278_, v_a_5286_, v_a_5288_, v_a_5289_);
if (lean_obj_tag(v___x_5291_) == 0)
{
lean_object* v_a_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v_a_5292_ = lean_ctor_get(v___x_5291_, 0);
lean_inc(v_a_5292_);
lean_dec_ref(v___x_5291_);
v___x_5293_ = l_Lean_mkFVar(v_fvarId_5278_);
v___x_5294_ = l_Lean_Meta_Grind_add(v_a_5292_, v___x_5293_, v_generation_5279_, v_a_5280_, v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
return v___x_5294_;
}
else
{
lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5302_; 
lean_dec(v_generation_5279_);
lean_dec(v_fvarId_5278_);
v_a_5295_ = lean_ctor_get(v___x_5291_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5291_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5297_ = v___x_5291_;
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_dec(v___x_5291_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5303_, lean_object* v_generation_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_){
_start:
{
lean_object* v_res_5316_; 
v_res_5316_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5303_, v_generation_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_);
lean_dec(v_a_5314_);
lean_dec_ref(v_a_5313_);
lean_dec(v_a_5312_);
lean_dec_ref(v_a_5311_);
lean_dec(v_a_5310_);
lean_dec_ref(v_a_5309_);
lean_dec(v_a_5308_);
lean_dec_ref(v_a_5307_);
lean_dec(v_a_5306_);
lean_dec(v_a_5305_);
return v_res_5316_;
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
