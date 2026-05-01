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
lean_object* v_a_13_; lean_object* v_self_14_; lean_object* v_next_15_; lean_object* v_root_16_; lean_object* v_congr_17_; lean_object* v_target_x3f_18_; lean_object* v_proof_x3f_19_; uint8_t v_flipped_20_; lean_object* v_size_21_; uint8_t v_interpreted_22_; uint8_t v_ctor_23_; uint8_t v_hasLambdas_24_; uint8_t v_heqProofs_25_; lean_object* v_idx_26_; lean_object* v_generation_27_; lean_object* v_mt_28_; lean_object* v_sTerms_29_; uint8_t v_funCC_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_53_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_13_);
lean_dec_ref(v___x_12_);
v_self_14_ = lean_ctor_get(v_a_13_, 0);
v_next_15_ = lean_ctor_get(v_a_13_, 1);
v_root_16_ = lean_ctor_get(v_a_13_, 2);
v_congr_17_ = lean_ctor_get(v_a_13_, 3);
v_target_x3f_18_ = lean_ctor_get(v_a_13_, 4);
v_proof_x3f_19_ = lean_ctor_get(v_a_13_, 5);
v_flipped_20_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11);
v_size_21_ = lean_ctor_get(v_a_13_, 6);
v_interpreted_22_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11 + 1);
v_ctor_23_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11 + 2);
v_hasLambdas_24_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11 + 3);
v_heqProofs_25_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11 + 4);
v_idx_26_ = lean_ctor_get(v_a_13_, 7);
v_generation_27_ = lean_ctor_get(v_a_13_, 8);
v_mt_28_ = lean_ctor_get(v_a_13_, 9);
v_sTerms_29_ = lean_ctor_get(v_a_13_, 10);
v_funCC_30_ = lean_ctor_get_uint8(v_a_13_, sizeof(void*)*11 + 5);
v_isSharedCheck_53_ = !lean_is_exclusive(v_a_13_);
if (v_isSharedCheck_53_ == 0)
{
v___x_32_ = v_a_13_;
v_isShared_33_ = v_isSharedCheck_53_;
goto v_resetjp_31_;
}
else
{
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
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_53_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___y_35_; 
if (lean_obj_tag(v_target_x3f_18_) == 1)
{
lean_object* v_val_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_52_; 
v_val_40_ = lean_ctor_get(v_target_x3f_18_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v_target_x3f_18_);
if (v_isSharedCheck_52_ == 0)
{
v___x_42_ = v_target_x3f_18_;
v_isShared_43_ = v_isSharedCheck_52_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_val_40_);
lean_dec(v_target_x3f_18_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_52_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
uint8_t v___y_45_; 
if (v_flipped_20_ == 0)
{
uint8_t v___x_50_; 
v___x_50_ = 1;
v___y_45_ = v___x_50_;
goto v___jp_44_;
}
else
{
uint8_t v___x_51_; 
v___x_51_ = 0;
v___y_45_ = v___x_51_;
goto v___jp_44_;
}
v___jp_44_:
{
lean_object* v___x_47_; 
lean_inc_ref(v_e_1_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v_e_1_);
v___x_47_ = v___x_42_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_e_1_);
v___x_47_ = v_reuseFailAlloc_49_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_val_40_, v___y_45_, v___x_47_, v_proof_x3f_19_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_dec_ref(v___x_48_);
v___y_35_ = v_a_5_;
goto v___jp_34_;
}
else
{
lean_del_object(v___x_32_);
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
return v___x_48_;
}
}
}
}
}
else
{
lean_dec(v_proof_x3f_19_);
lean_dec(v_target_x3f_18_);
v___y_35_ = v_a_5_;
goto v___jp_34_;
}
v___jp_34_:
{
lean_object* v___x_37_; 
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 5, v_proofNew_x3f_4_);
lean_ctor_set(v___x_32_, 4, v_targetNew_x3f_3_);
v___x_37_ = v___x_32_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_self_14_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_next_15_);
lean_ctor_set(v_reuseFailAlloc_39_, 2, v_root_16_);
lean_ctor_set(v_reuseFailAlloc_39_, 3, v_congr_17_);
lean_ctor_set(v_reuseFailAlloc_39_, 4, v_targetNew_x3f_3_);
lean_ctor_set(v_reuseFailAlloc_39_, 5, v_proofNew_x3f_4_);
lean_ctor_set(v_reuseFailAlloc_39_, 6, v_size_21_);
lean_ctor_set(v_reuseFailAlloc_39_, 7, v_idx_26_);
lean_ctor_set(v_reuseFailAlloc_39_, 8, v_generation_27_);
lean_ctor_set(v_reuseFailAlloc_39_, 9, v_mt_28_);
lean_ctor_set(v_reuseFailAlloc_39_, 10, v_sTerms_29_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*11 + 1, v_interpreted_22_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*11 + 2, v_ctor_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*11 + 3, v_hasLambdas_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*11 + 4, v_heqProofs_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*11 + 5, v_funCC_30_);
v___x_37_ = v_reuseFailAlloc_39_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; 
lean_ctor_set_uint8(v___x_37_, sizeof(void*)*11, v_flippedNew_2_);
v___x_38_ = l_Lean_Meta_Grind_setENode___redArg(v_e_1_, v___x_37_, v___y_35_);
return v___x_38_;
}
}
}
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_dec(v_proofNew_x3f_4_);
lean_dec(v_targetNew_x3f_3_);
lean_dec_ref(v_e_1_);
v_a_54_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_12_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_12_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg___boxed(lean_object* v_e_62_, lean_object* v_flippedNew_63_, lean_object* v_targetNew_x3f_64_, lean_object* v_proofNew_x3f_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
uint8_t v_flippedNew_boxed_72_; lean_object* v_res_73_; 
v_flippedNew_boxed_72_ = lean_unbox(v_flippedNew_63_);
v_res_73_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_62_, v_flippedNew_boxed_72_, v_targetNew_x3f_64_, v_proofNew_x3f_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(lean_object* v_e_74_, uint8_t v_flippedNew_75_, lean_object* v_targetNew_x3f_76_, lean_object* v_proofNew_x3f_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_74_, v_flippedNew_75_, v_targetNew_x3f_76_, v_proofNew_x3f_77_, v_a_78_, v_a_84_, v_a_85_, v_a_86_, v_a_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___boxed(lean_object* v_e_90_, lean_object* v_flippedNew_91_, lean_object* v_targetNew_x3f_92_, lean_object* v_proofNew_x3f_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
uint8_t v_flippedNew_boxed_105_; lean_object* v_res_106_; 
v_flippedNew_boxed_105_ = lean_unbox(v_flippedNew_91_);
v_res_106_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go(v_e_90_, v_flippedNew_boxed_105_, v_targetNew_x3f_92_, v_proofNew_x3f_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec(v_a_94_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(lean_object* v_e_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = 0;
v___x_115_ = lean_box(0);
v___x_116_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans_go___redArg(v_e_107_, v___x_114_, v___x_115_, v___x_115_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg___boxed(lean_object* v_e_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_e_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(lean_object* v_e_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_e_125_, v_a_126_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___boxed(lean_object* v_e_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans(v_e_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec(v_a_139_);
return v_res_150_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(lean_object* v_parent_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = l_Lean_Expr_isApp(v_parent_151_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = l_Lean_Expr_isArrow(v_parent_151_);
return v___x_153_;
}
else
{
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant___boxed(lean_object* v_parent_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_parent_154_);
lean_dec_ref(v_parent_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(lean_object* v_msgData_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; lean_object* v_env_164_; lean_object* v___x_165_; lean_object* v_mctx_166_; lean_object* v_lctx_167_; lean_object* v_options_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_163_ = lean_st_ref_get(v___y_161_);
v_env_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_env_164_);
lean_dec(v___x_163_);
v___x_165_ = lean_st_ref_get(v___y_159_);
v_mctx_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc_ref(v_mctx_166_);
lean_dec(v___x_165_);
v_lctx_167_ = lean_ctor_get(v___y_158_, 2);
v_options_168_ = lean_ctor_get(v___y_160_, 2);
lean_inc_ref(v_options_168_);
lean_inc_ref(v_lctx_167_);
v___x_169_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_169_, 0, v_env_164_);
lean_ctor_set(v___x_169_, 1, v_mctx_166_);
lean_ctor_set(v___x_169_, 2, v_lctx_167_);
lean_ctor_set(v___x_169_, 3, v_options_168_);
v___x_170_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_msgData_157_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2___boxed(lean_object* v_msgData_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msgData_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_178_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_179_; double v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = lean_float_of_nat(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object* v_cls_184_, lean_object* v_msg_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_ref_191_; lean_object* v___x_192_; lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_237_; 
v_ref_191_ = lean_ctor_get(v___y_188_, 5);
v___x_192_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msg_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_237_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_237_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_237_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v_traceState_198_; lean_object* v_env_199_; lean_object* v_nextMacroScope_200_; lean_object* v_ngen_201_; lean_object* v_auxDeclNGen_202_; lean_object* v_cache_203_; lean_object* v_messages_204_; lean_object* v_infoState_205_; lean_object* v_snapshotTasks_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_236_; 
v___x_197_ = lean_st_ref_take(v___y_189_);
v_traceState_198_ = lean_ctor_get(v___x_197_, 4);
v_env_199_ = lean_ctor_get(v___x_197_, 0);
v_nextMacroScope_200_ = lean_ctor_get(v___x_197_, 1);
v_ngen_201_ = lean_ctor_get(v___x_197_, 2);
v_auxDeclNGen_202_ = lean_ctor_get(v___x_197_, 3);
v_cache_203_ = lean_ctor_get(v___x_197_, 5);
v_messages_204_ = lean_ctor_get(v___x_197_, 6);
v_infoState_205_ = lean_ctor_get(v___x_197_, 7);
v_snapshotTasks_206_ = lean_ctor_get(v___x_197_, 8);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_236_ == 0)
{
v___x_208_ = v___x_197_;
v_isShared_209_ = v_isSharedCheck_236_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_snapshotTasks_206_);
lean_inc(v_infoState_205_);
lean_inc(v_messages_204_);
lean_inc(v_cache_203_);
lean_inc(v_traceState_198_);
lean_inc(v_auxDeclNGen_202_);
lean_inc(v_ngen_201_);
lean_inc(v_nextMacroScope_200_);
lean_inc(v_env_199_);
lean_dec(v___x_197_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_236_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
uint64_t v_tid_210_; lean_object* v_traces_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_235_; 
v_tid_210_ = lean_ctor_get_uint64(v_traceState_198_, sizeof(void*)*1);
v_traces_211_ = lean_ctor_get(v_traceState_198_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_traceState_198_);
if (v_isSharedCheck_235_ == 0)
{
v___x_213_ = v_traceState_198_;
v_isShared_214_ = v_isSharedCheck_235_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_traces_211_);
lean_dec(v_traceState_198_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_235_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; double v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_215_ = lean_box(0);
v___x_216_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0);
v___x_217_ = 0;
v___x_218_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
v___x_219_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_219_, 0, v_cls_184_);
lean_ctor_set(v___x_219_, 1, v___x_215_);
lean_ctor_set(v___x_219_, 2, v___x_218_);
lean_ctor_set_float(v___x_219_, sizeof(void*)*3, v___x_216_);
lean_ctor_set_float(v___x_219_, sizeof(void*)*3 + 8, v___x_216_);
lean_ctor_set_uint8(v___x_219_, sizeof(void*)*3 + 16, v___x_217_);
v___x_220_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2));
v___x_221_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v_a_193_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
lean_inc(v_ref_191_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_ref_191_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = l_Lean_PersistentArray_push___redArg(v_traces_211_, v___x_222_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_223_);
v___x_225_ = v___x_213_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_223_);
lean_ctor_set_uint64(v_reuseFailAlloc_234_, sizeof(void*)*1, v_tid_210_);
v___x_225_ = v_reuseFailAlloc_234_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_227_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 4, v___x_225_);
v___x_227_ = v___x_208_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_env_199_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_nextMacroScope_200_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_ngen_201_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v_auxDeclNGen_202_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_233_, 5, v_cache_203_);
lean_ctor_set(v_reuseFailAlloc_233_, 6, v_messages_204_);
lean_ctor_set(v_reuseFailAlloc_233_, 7, v_infoState_205_);
lean_ctor_set(v_reuseFailAlloc_233_, 8, v_snapshotTasks_206_);
v___x_227_ = v_reuseFailAlloc_233_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_228_ = lean_st_ref_set(v___y_189_, v___x_227_);
v___x_229_ = lean_box(0);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_229_);
v___x_231_ = v___x_195_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object* v_cls_238_, lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_238_, v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(lean_object* v___x_246_, lean_object* v_xs_247_, lean_object* v_v_248_, lean_object* v_i_249_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_array_get_size(v_xs_247_);
v___x_251_ = lean_nat_dec_lt(v_i_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec(v_i_249_);
lean_dec_ref(v_v_248_);
v___x_252_ = lean_box(0);
return v___x_252_;
}
else
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_array_fget_borrowed(v_xs_247_, v_i_249_);
lean_inc_ref(v_v_248_);
lean_inc(v___x_253_);
v___x_254_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_246_, v___x_253_, v_v_248_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_i_249_, v___x_255_);
lean_dec(v_i_249_);
v_i_249_ = v___x_256_;
goto _start;
}
else
{
lean_object* v___x_258_; 
lean_dec_ref(v_v_248_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_i_249_);
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v___x_259_, lean_object* v_xs_260_, lean_object* v_v_261_, lean_object* v_i_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_259_, v_xs_260_, v_v_261_, v_i_262_);
lean_dec_ref(v_xs_260_);
lean_dec_ref(v___x_259_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(lean_object* v___x_264_, lean_object* v_xs_265_, lean_object* v_v_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_264_, v_xs_265_, v_v_266_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1___boxed(lean_object* v___x_269_, lean_object* v_xs_270_, lean_object* v_v_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_269_, v_xs_270_, v_v_271_);
lean_dec_ref(v_xs_270_);
lean_dec_ref(v___x_269_);
return v_res_272_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_273_; size_t v___x_274_; size_t v___x_275_; 
v___x_273_ = ((size_t)5ULL);
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_shift_left(v___x_274_, v___x_273_);
return v___x_275_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; 
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0);
v___x_278_ = lean_usize_sub(v___x_277_, v___x_276_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* v___x_279_, lean_object* v_x_280_, size_t v_x_281_, lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_280_) == 0)
{
lean_object* v_es_283_; lean_object* v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; lean_object* v_j_288_; lean_object* v_entry_289_; 
v_es_283_ = lean_ctor_get(v_x_280_, 0);
v___x_284_ = lean_box(2);
v___x_285_ = ((size_t)5ULL);
v___x_286_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_287_ = lean_usize_land(v_x_281_, v___x_286_);
v_j_288_ = lean_usize_to_nat(v___x_287_);
v_entry_289_ = lean_array_get(v___x_284_, v_es_283_, v_j_288_);
switch(lean_obj_tag(v_entry_289_))
{
case 0:
{
lean_object* v_key_290_; uint8_t v___x_291_; 
v_key_290_ = lean_ctor_get(v_entry_289_, 0);
lean_inc(v_key_290_);
lean_dec_ref(v_entry_289_);
v___x_291_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_279_, v_x_282_, v_key_290_);
if (v___x_291_ == 0)
{
lean_dec(v_j_288_);
return v_x_280_;
}
else
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
lean_inc_ref(v_es_283_);
v_isSharedCheck_299_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v_x_280_, 0);
lean_dec(v_unused_300_);
v___x_293_ = v_x_280_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_dec(v_x_280_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_array_set(v_es_283_, v_j_288_, v___x_284_);
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
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_334_; 
lean_inc_ref(v_es_283_);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_x_280_, 0);
lean_dec(v_unused_335_);
v___x_302_ = v_x_280_;
v_isShared_303_ = v_isSharedCheck_334_;
goto v_resetjp_301_;
}
else
{
lean_dec(v_x_280_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_334_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_node_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_333_; 
v_node_304_ = lean_ctor_get(v_entry_289_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_entry_289_);
if (v_isSharedCheck_333_ == 0)
{
v___x_306_ = v_entry_289_;
v_isShared_307_ = v_isSharedCheck_333_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_node_304_);
lean_dec(v_entry_289_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_333_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v_entries_308_; size_t v___x_309_; lean_object* v_newNode_310_; lean_object* v___x_311_; 
v_entries_308_ = lean_array_set(v_es_283_, v_j_288_, v___x_284_);
v___x_309_ = lean_usize_shift_right(v_x_281_, v___x_285_);
v_newNode_310_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_279_, v_node_304_, v___x_309_, v_x_282_);
lean_inc_ref(v_newNode_310_);
v___x_311_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_310_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_313_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v_newNode_310_);
v___x_313_ = v___x_306_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_newNode_310_);
v___x_313_ = v_reuseFailAlloc_318_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = lean_array_set(v_entries_308_, v_j_288_, v___x_313_);
lean_dec(v_j_288_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_314_);
v___x_316_ = v___x_302_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
else
{
lean_object* v_val_319_; lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v_newNode_310_);
lean_del_object(v___x_306_);
v_val_319_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_val_319_);
lean_dec_ref(v___x_311_);
v_fst_320_ = lean_ctor_get(v_val_319_, 0);
v_snd_321_ = lean_ctor_get(v_val_319_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_val_319_);
if (v_isSharedCheck_332_ == 0)
{
v___x_323_ = v_val_319_;
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_snd_321_);
lean_inc(v_fst_320_);
lean_dec(v_val_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_fst_320_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_snd_321_);
v___x_326_ = v_reuseFailAlloc_331_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_array_set(v_entries_308_, v_j_288_, v___x_326_);
lean_dec(v_j_288_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_327_);
v___x_329_ = v___x_302_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
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
lean_dec_ref(v_x_282_);
return v_x_280_;
}
}
}
else
{
lean_object* v_ks_336_; lean_object* v_vs_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_351_; 
v_ks_336_ = lean_ctor_get(v_x_280_, 0);
v_vs_337_ = lean_ctor_get(v_x_280_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_x_280_);
if (v_isSharedCheck_351_ == 0)
{
v___x_339_ = v_x_280_;
v_isShared_340_ = v_isSharedCheck_351_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_vs_337_);
lean_inc(v_ks_336_);
lean_dec(v_x_280_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_351_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; 
v___x_341_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_279_, v_ks_336_, v_x_282_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v___x_343_; 
if (v_isShared_340_ == 0)
{
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_ks_336_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_vs_337_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
lean_object* v_val_345_; lean_object* v_keys_x27_346_; lean_object* v_vals_x27_347_; lean_object* v___x_349_; 
v_val_345_ = lean_ctor_get(v___x_341_, 0);
lean_inc_n(v_val_345_, 2);
lean_dec_ref(v___x_341_);
v_keys_x27_346_ = l_Array_eraseIdx___redArg(v_ks_336_, v_val_345_);
v_vals_x27_347_ = l_Array_eraseIdx___redArg(v_vs_337_, v_val_345_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v_vals_x27_347_);
lean_ctor_set(v___x_339_, 0, v_keys_x27_346_);
v___x_349_ = v___x_339_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_keys_x27_346_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_vals_x27_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* v___x_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
size_t v_x_28249__boxed_356_; lean_object* v_res_357_; 
v_x_28249__boxed_356_ = lean_unbox_usize(v_x_354_);
lean_dec(v_x_354_);
v_res_357_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_352_, v_x_353_, v_x_28249__boxed_356_, v_x_355_);
lean_dec_ref(v___x_352_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
uint64_t v___x_361_; size_t v_h_362_; lean_object* v___x_363_; 
lean_inc_ref(v_x_360_);
v___x_361_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_358_, v_x_360_);
v_h_362_ = lean_uint64_to_usize(v___x_361_);
v___x_363_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_358_, v_x_359_, v_h_362_, v_x_360_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg___boxed(lean_object* v___x_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_364_, v_x_365_, v_x_366_);
lean_dec_ref(v___x_364_);
return v_res_367_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_379_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_380_ = l_Lean_Name_append(v___x_379_, v___x_378_);
return v___x_380_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object* v_as_x27_384_, lean_object* v_b_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
if (lean_obj_tag(v_as_x27_384_) == 0)
{
lean_object* v___x_397_; 
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v_b_385_);
return v___x_397_;
}
else
{
lean_object* v_head_398_; lean_object* v_tail_399_; lean_object* v___x_400_; lean_object* v___y_402_; uint8_t v_a_442_; uint8_t v___x_455_; 
v_head_398_ = lean_ctor_get(v_as_x27_384_, 0);
v_tail_399_ = lean_ctor_get(v_as_x27_384_, 1);
v___x_400_ = lean_box(0);
v___x_455_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_398_);
if (v___x_455_ == 0)
{
v_a_442_ = v___x_455_;
goto v___jp_441_;
}
else
{
lean_object* v___x_456_; 
lean_inc(v_head_398_);
v___x_456_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_398_, v___y_386_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; uint8_t v___x_458_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref(v___x_456_);
v___x_458_ = lean_unbox(v_a_457_);
lean_dec(v_a_457_);
v_a_442_ = v___x_458_;
goto v___jp_441_;
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_a_459_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_456_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_456_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
v___jp_401_:
{
lean_object* v___x_403_; lean_object* v_toGoalState_404_; lean_object* v_mvarId_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_440_; 
v___x_403_ = lean_st_ref_take(v___y_402_);
v_toGoalState_404_ = lean_ctor_get(v___x_403_, 0);
v_mvarId_405_ = lean_ctor_get(v___x_403_, 1);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_440_ == 0)
{
v___x_407_ = v___x_403_;
v_isShared_408_ = v_isSharedCheck_440_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_mvarId_405_);
lean_inc(v_toGoalState_404_);
lean_dec(v___x_403_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_440_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_nextDeclIdx_409_; lean_object* v_enodeMap_410_; lean_object* v_exprs_411_; lean_object* v_parents_412_; lean_object* v_congrTable_413_; lean_object* v_appMap_414_; lean_object* v_indicesFound_415_; lean_object* v_newFacts_416_; uint8_t v_inconsistent_417_; lean_object* v_nextIdx_418_; lean_object* v_newRawFacts_419_; lean_object* v_facts_420_; lean_object* v_extThms_421_; lean_object* v_ematch_422_; lean_object* v_inj_423_; lean_object* v_split_424_; lean_object* v_clean_425_; lean_object* v_sstates_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_439_; 
v_nextDeclIdx_409_ = lean_ctor_get(v_toGoalState_404_, 0);
v_enodeMap_410_ = lean_ctor_get(v_toGoalState_404_, 1);
v_exprs_411_ = lean_ctor_get(v_toGoalState_404_, 2);
v_parents_412_ = lean_ctor_get(v_toGoalState_404_, 3);
v_congrTable_413_ = lean_ctor_get(v_toGoalState_404_, 4);
v_appMap_414_ = lean_ctor_get(v_toGoalState_404_, 5);
v_indicesFound_415_ = lean_ctor_get(v_toGoalState_404_, 6);
v_newFacts_416_ = lean_ctor_get(v_toGoalState_404_, 7);
v_inconsistent_417_ = lean_ctor_get_uint8(v_toGoalState_404_, sizeof(void*)*17);
v_nextIdx_418_ = lean_ctor_get(v_toGoalState_404_, 8);
v_newRawFacts_419_ = lean_ctor_get(v_toGoalState_404_, 9);
v_facts_420_ = lean_ctor_get(v_toGoalState_404_, 10);
v_extThms_421_ = lean_ctor_get(v_toGoalState_404_, 11);
v_ematch_422_ = lean_ctor_get(v_toGoalState_404_, 12);
v_inj_423_ = lean_ctor_get(v_toGoalState_404_, 13);
v_split_424_ = lean_ctor_get(v_toGoalState_404_, 14);
v_clean_425_ = lean_ctor_get(v_toGoalState_404_, 15);
v_sstates_426_ = lean_ctor_get(v_toGoalState_404_, 16);
v_isSharedCheck_439_ = !lean_is_exclusive(v_toGoalState_404_);
if (v_isSharedCheck_439_ == 0)
{
v___x_428_ = v_toGoalState_404_;
v_isShared_429_ = v_isSharedCheck_439_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_sstates_426_);
lean_inc(v_clean_425_);
lean_inc(v_split_424_);
lean_inc(v_inj_423_);
lean_inc(v_ematch_422_);
lean_inc(v_extThms_421_);
lean_inc(v_facts_420_);
lean_inc(v_newRawFacts_419_);
lean_inc(v_nextIdx_418_);
lean_inc(v_newFacts_416_);
lean_inc(v_indicesFound_415_);
lean_inc(v_appMap_414_);
lean_inc(v_congrTable_413_);
lean_inc(v_parents_412_);
lean_inc(v_exprs_411_);
lean_inc(v_enodeMap_410_);
lean_inc(v_nextDeclIdx_409_);
lean_dec(v_toGoalState_404_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_439_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_inc(v_head_398_);
v___x_430_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_410_, v_congrTable_413_, v_head_398_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 4, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_nextDeclIdx_409_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_enodeMap_410_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_exprs_411_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_parents_412_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_438_, 5, v_appMap_414_);
lean_ctor_set(v_reuseFailAlloc_438_, 6, v_indicesFound_415_);
lean_ctor_set(v_reuseFailAlloc_438_, 7, v_newFacts_416_);
lean_ctor_set(v_reuseFailAlloc_438_, 8, v_nextIdx_418_);
lean_ctor_set(v_reuseFailAlloc_438_, 9, v_newRawFacts_419_);
lean_ctor_set(v_reuseFailAlloc_438_, 10, v_facts_420_);
lean_ctor_set(v_reuseFailAlloc_438_, 11, v_extThms_421_);
lean_ctor_set(v_reuseFailAlloc_438_, 12, v_ematch_422_);
lean_ctor_set(v_reuseFailAlloc_438_, 13, v_inj_423_);
lean_ctor_set(v_reuseFailAlloc_438_, 14, v_split_424_);
lean_ctor_set(v_reuseFailAlloc_438_, 15, v_clean_425_);
lean_ctor_set(v_reuseFailAlloc_438_, 16, v_sstates_426_);
lean_ctor_set_uint8(v_reuseFailAlloc_438_, sizeof(void*)*17, v_inconsistent_417_);
v___x_432_ = v_reuseFailAlloc_438_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_432_);
v___x_434_ = v___x_407_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_mvarId_405_);
v___x_434_ = v_reuseFailAlloc_437_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; 
v___x_435_ = lean_st_ref_set(v___y_402_, v___x_434_);
v_as_x27_384_ = v_tail_399_;
v_b_385_ = v___x_400_;
goto _start;
}
}
}
}
}
v___jp_441_:
{
if (v_a_442_ == 0)
{
v_as_x27_384_ = v_tail_399_;
v_b_385_ = v___x_400_;
goto _start;
}
else
{
lean_object* v_options_444_; uint8_t v_hasTrace_445_; 
v_options_444_ = lean_ctor_get(v___y_394_, 2);
v_hasTrace_445_ = lean_ctor_get_uint8(v_options_444_, sizeof(void*)*1);
if (v_hasTrace_445_ == 0)
{
v___y_402_ = v___y_386_;
goto v___jp_401_;
}
else
{
lean_object* v_inheritedTraceOptions_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_inheritedTraceOptions_446_ = lean_ctor_get(v___y_394_, 13);
v___x_447_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_448_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_449_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_446_, v_options_444_, v___x_448_);
if (v___x_449_ == 0)
{
v___y_402_ = v___y_386_;
goto v___jp_401_;
}
else
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_Grind_updateLastTag(v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec_ref(v___x_450_);
v___x_451_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_398_);
v___x_452_ = l_Lean_MessageData_ofExpr(v_head_398_);
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_447_, v___x_453_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_dec_ref(v___x_454_);
v___y_402_ = v___y_386_;
goto v___jp_401_;
}
else
{
return v___x_454_;
}
}
else
{
return v___x_450_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_467_, lean_object* v_b_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_467_, v_b_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec(v___y_469_);
lean_dec(v_as_x27_467_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Meta_Grind_getParents___redArg(v_root_481_, v_a_482_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref(v___x_493_);
v___x_495_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_494_);
v___x_496_ = lean_box(0);
v___x_497_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_495_, v___x_496_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
lean_dec(v___x_495_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v___x_497_, 0);
lean_dec(v_unused_505_);
v___x_499_ = v___x_497_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_dec(v___x_497_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v_a_494_);
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_494_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_dec(v_a_494_);
v_a_506_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_497_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_497_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_root_514_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_527_, lean_object* v_00_u03b2_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_527_, v_x_529_, v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_532_, lean_object* v_00_u03b2_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_532_, v_00_u03b2_533_, v_x_534_, v_x_535_);
lean_dec_ref(v___x_532_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_537_, lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_537_, v_msg_538_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_551_, lean_object* v_msg_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_551_, v_msg_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec(v___y_553_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_565_, lean_object* v_as_x27_566_, lean_object* v_b_567_, lean_object* v_a_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_566_, v_b_567_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_581_, lean_object* v_as_x27_582_, lean_object* v_b_583_, lean_object* v_a_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_581_, v_as_x27_582_, v_b_583_, v_a_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec(v___y_585_);
lean_dec(v_as_x27_582_);
lean_dec(v_as_581_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_597_, lean_object* v_00_u03b2_598_, lean_object* v_x_599_, size_t v_x_600_, lean_object* v_x_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_597_, v_x_599_, v_x_600_, v_x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_603_, lean_object* v_00_u03b2_604_, lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v_x_607_){
_start:
{
size_t v_x_28717__boxed_608_; lean_object* v_res_609_; 
v_x_28717__boxed_608_ = lean_unbox_usize(v_x_606_);
lean_dec(v_x_606_);
v_res_609_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_603_, v_00_u03b2_604_, v_x_605_, v_x_28717__boxed_608_, v_x_607_);
lean_dec_ref(v___x_603_);
return v_res_609_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_612_ = l_Lean_stringToMessageData(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_613_, lean_object* v_b_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
if (lean_obj_tag(v_as_x27_613_) == 0)
{
lean_object* v___x_626_; 
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v_b_614_);
return v___x_626_;
}
else
{
lean_object* v_head_627_; lean_object* v_tail_628_; lean_object* v___x_629_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; uint8_t v_a_644_; uint8_t v___x_657_; 
v_head_627_ = lean_ctor_get(v_as_x27_613_, 0);
v_tail_628_ = lean_ctor_get(v_as_x27_613_, 1);
v___x_629_ = lean_box(0);
v___x_657_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_627_);
if (v___x_657_ == 0)
{
v_a_644_ = v___x_657_;
goto v___jp_643_;
}
else
{
lean_object* v___x_658_; 
lean_inc(v_head_627_);
v___x_658_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_627_, v___y_615_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; uint8_t v___x_660_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref(v___x_658_);
v___x_660_ = lean_unbox(v_a_659_);
lean_dec(v_a_659_);
v_a_644_ = v___x_660_;
goto v___jp_643_;
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_658_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_658_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
v___jp_630_:
{
lean_object* v___x_641_; 
lean_inc(v_head_627_);
v___x_641_ = l_Lean_Meta_Grind_addCongrTable(v_head_627_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_dec_ref(v___x_641_);
v_as_x27_613_ = v_tail_628_;
v_b_614_ = v___x_629_;
goto _start;
}
else
{
return v___x_641_;
}
}
v___jp_643_:
{
if (v_a_644_ == 0)
{
v_as_x27_613_ = v_tail_628_;
v_b_614_ = v___x_629_;
goto _start;
}
else
{
lean_object* v_options_646_; uint8_t v_hasTrace_647_; 
v_options_646_ = lean_ctor_get(v___y_623_, 2);
v_hasTrace_647_ = lean_ctor_get_uint8(v_options_646_, sizeof(void*)*1);
if (v_hasTrace_647_ == 0)
{
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
goto v___jp_630_;
}
else
{
lean_object* v_inheritedTraceOptions_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_inheritedTraceOptions_648_ = lean_ctor_get(v___y_623_, 13);
v___x_649_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_650_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_651_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_648_, v_options_646_, v___x_650_);
if (v___x_651_ == 0)
{
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
goto v___jp_630_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Meta_Grind_updateLastTag(v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec_ref(v___x_652_);
v___x_653_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_627_);
v___x_654_ = l_Lean_MessageData_ofExpr(v_head_627_);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_649_, v___x_655_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_dec_ref(v___x_656_);
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
v___y_639_ = v___y_623_;
v___y_640_ = v___y_624_;
goto v___jp_630_;
}
else
{
return v___x_656_;
}
}
else
{
return v___x_652_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_669_, lean_object* v_b_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_669_, v_b_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec(v___y_671_);
lean_dec(v_as_x27_669_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_683_);
v___x_696_ = lean_box(0);
v___x_697_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_695_, v___x_696_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
lean_dec(v___x_695_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_697_, 0);
lean_dec(v_unused_705_);
v___x_699_ = v___x_697_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_dec(v___x_697_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_696_);
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_696_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
else
{
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec(v_a_707_);
lean_dec(v_parents_706_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_719_, lean_object* v_as_x27_720_, lean_object* v_b_721_, lean_object* v_a_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_720_, v_b_721_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_735_, lean_object* v_as_x27_736_, lean_object* v_b_737_, lean_object* v_a_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_735_, v_as_x27_736_, v_b_737_, v_a_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec(v___y_739_);
lean_dec(v_as_x27_736_);
lean_dec(v_as_735_);
return v_res_750_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_751_, lean_object* v_i_752_, lean_object* v_k_753_){
_start:
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = lean_array_get_size(v_keys_751_);
v___x_755_ = lean_nat_dec_lt(v_i_752_, v___x_754_);
if (v___x_755_ == 0)
{
lean_dec(v_i_752_);
return v___x_755_;
}
else
{
lean_object* v_k_x27_756_; uint8_t v___x_757_; 
v_k_x27_756_ = lean_array_fget_borrowed(v_keys_751_, v_i_752_);
v___x_757_ = l_Lean_instBEqMVarId_beq(v_k_753_, v_k_x27_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = lean_nat_add(v_i_752_, v___x_758_);
lean_dec(v_i_752_);
v_i_752_ = v___x_759_;
goto _start;
}
else
{
lean_dec(v_i_752_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_761_, lean_object* v_i_762_, lean_object* v_k_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_761_, v_i_762_, v_k_763_);
lean_dec(v_k_763_);
lean_dec_ref(v_keys_761_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_766_, size_t v_x_767_, lean_object* v_x_768_){
_start:
{
if (lean_obj_tag(v_x_766_) == 0)
{
lean_object* v_es_769_; lean_object* v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; lean_object* v_j_774_; lean_object* v___x_775_; 
v_es_769_ = lean_ctor_get(v_x_766_, 0);
v___x_770_ = lean_box(2);
v___x_771_ = ((size_t)5ULL);
v___x_772_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_773_ = lean_usize_land(v_x_767_, v___x_772_);
v_j_774_ = lean_usize_to_nat(v___x_773_);
v___x_775_ = lean_array_get_borrowed(v___x_770_, v_es_769_, v_j_774_);
lean_dec(v_j_774_);
switch(lean_obj_tag(v___x_775_))
{
case 0:
{
lean_object* v_key_776_; uint8_t v___x_777_; 
v_key_776_ = lean_ctor_get(v___x_775_, 0);
v___x_777_ = l_Lean_instBEqMVarId_beq(v_x_768_, v_key_776_);
return v___x_777_;
}
case 1:
{
lean_object* v_node_778_; size_t v___x_779_; 
v_node_778_ = lean_ctor_get(v___x_775_, 0);
v___x_779_ = lean_usize_shift_right(v_x_767_, v___x_771_);
v_x_766_ = v_node_778_;
v_x_767_ = v___x_779_;
goto _start;
}
default: 
{
uint8_t v___x_781_; 
v___x_781_ = 0;
return v___x_781_;
}
}
}
else
{
lean_object* v_ks_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_ks_782_ = lean_ctor_get(v_x_766_, 0);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_782_, v___x_783_, v_x_768_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
size_t v_x_10242__boxed_788_; uint8_t v_res_789_; lean_object* v_r_790_; 
v_x_10242__boxed_788_ = lean_unbox_usize(v_x_786_);
lean_dec(v_x_786_);
v_res_789_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_785_, v_x_10242__boxed_788_, v_x_787_);
lean_dec(v_x_787_);
lean_dec_ref(v_x_785_);
v_r_790_ = lean_box(v_res_789_);
return v_r_790_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
uint64_t v___x_793_; size_t v___x_794_; uint8_t v___x_795_; 
v___x_793_ = l_Lean_instHashableMVarId_hash(v_x_792_);
v___x_794_ = lean_uint64_to_usize(v___x_793_);
v___x_795_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_791_, v___x_794_, v_x_792_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_796_, v_x_797_);
lean_dec(v_x_797_);
lean_dec_ref(v_x_796_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; lean_object* v_mctx_804_; lean_object* v_eAssignment_805_; uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_803_ = lean_st_ref_get(v___y_801_);
v_mctx_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc_ref(v_mctx_804_);
lean_dec(v___x_803_);
v_eAssignment_805_ = lean_ctor_get(v_mctx_804_, 8);
lean_inc_ref(v_eAssignment_805_);
lean_dec_ref(v_mctx_804_);
v___x_806_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_805_, v_mvarId_800_);
lean_dec_ref(v_eAssignment_805_);
v___x_807_ = lean_box(v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec(v_mvarId_809_);
return v_res_812_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_823_ = l_Lean_mkConst(v___x_822_, v___x_821_);
return v___x_823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_box(0);
v___x_830_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_831_ = l_Lean_mkConst(v___x_830_, v___x_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; lean_object* v_mvarId_844_; lean_object* v___x_845_; lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_899_; 
v___x_843_ = lean_st_ref_get(v_a_832_);
v_mvarId_844_ = lean_ctor_get(v___x_843_, 1);
lean_inc(v_mvarId_844_);
lean_dec(v___x_843_);
v___x_845_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_844_, v_a_839_);
lean_dec(v_mvarId_844_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_899_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_899_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_899_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
uint8_t v___x_850_; 
v___x_850_ = lean_unbox(v_a_846_);
lean_dec(v_a_846_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_del_object(v___x_848_);
v___x_851_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_836_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref(v___x_851_);
v___x_853_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_852_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref(v___x_853_);
v___x_855_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_836_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref(v___x_855_);
v___x_857_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_836_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref(v___x_857_);
v___x_859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_861_ = l_Lean_mkApp4(v___x_859_, v_a_856_, v_a_858_, v_a_854_, v___x_860_);
v___x_862_ = l_Lean_Meta_Grind_closeGoal(v___x_861_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
return v___x_862_;
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec(v_a_856_);
lean_dec(v_a_854_);
v_a_863_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_857_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_857_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_a_854_);
v_a_871_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_855_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_855_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_853_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_853_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_a_887_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_851_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_851_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_895_);
v___x_897_ = v___x_848_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec(v_a_900_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_912_, v___y_920_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec(v___y_926_);
lean_dec(v_mvarId_925_);
return v_res_937_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_939_, v_x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
uint8_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_942_, v_x_943_, v_x_944_);
lean_dec(v_x_944_);
lean_dec_ref(v_x_943_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_947_, lean_object* v_x_948_, size_t v_x_949_, lean_object* v_x_950_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_948_, v_x_949_, v_x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
size_t v_x_10527__boxed_956_; uint8_t v_res_957_; lean_object* v_r_958_; 
v_x_10527__boxed_956_ = lean_unbox_usize(v_x_954_);
lean_dec(v_x_954_);
v_res_957_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_952_, v_x_953_, v_x_10527__boxed_956_, v_x_955_);
lean_dec(v_x_955_);
lean_dec_ref(v_x_953_);
v_r_958_ = lean_box(v_res_957_);
return v_r_958_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_959_, lean_object* v_keys_960_, lean_object* v_vals_961_, lean_object* v_heq_962_, lean_object* v_i_963_, lean_object* v_k_964_){
_start:
{
uint8_t v___x_965_; 
v___x_965_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_960_, v_i_963_, v_k_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_966_, lean_object* v_keys_967_, lean_object* v_vals_968_, lean_object* v_heq_969_, lean_object* v_i_970_, lean_object* v_k_971_){
_start:
{
uint8_t v_res_972_; lean_object* v_r_973_; 
v_res_972_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_966_, v_keys_967_, v_vals_968_, v_heq_969_, v_i_970_, v_k_971_);
lean_dec(v_k_971_);
lean_dec_ref(v_vals_968_);
lean_dec_ref(v_keys_967_);
v_r_973_ = lean_box(v_res_972_);
return v_r_973_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_box(0);
v___x_978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_979_ = l_Lean_mkConst(v___x_978_, v___x_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_980_, lean_object* v_rhs_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_993_; 
lean_inc_ref(v_rhs_981_);
lean_inc_ref(v_lhs_980_);
v___x_993_ = l_Lean_Meta_mkEq(v_lhs_980_, v_rhs_981_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref(v___x_993_);
lean_inc(v_a_991_);
lean_inc_ref(v_a_990_);
lean_inc(v_a_989_);
lean_inc_ref(v_a_988_);
lean_inc(v_a_987_);
lean_inc_ref(v_a_986_);
lean_inc(v_a_985_);
lean_inc_ref(v_a_984_);
lean_inc(v_a_983_);
lean_inc(v_a_982_);
v___x_995_ = lean_grind_mk_eq_proof(v_lhs_980_, v_rhs_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_997_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref(v___x_995_);
lean_inc(v_a_994_);
v___x_997_ = l_Lean_Meta_mkDecide(v_a_994_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v___x_997_);
v___x_999_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_986_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v___x_1001_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1002_ = l_Lean_Expr_appArg_x21(v_a_998_);
lean_dec(v_a_998_);
v___x_1003_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_994_);
v___x_1004_ = l_Lean_mkApp3(v___x_1001_, v_a_994_, v___x_1002_, v___x_1003_);
v___x_1005_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1006_ = l_Lean_mkApp4(v___x_1005_, v_a_994_, v_a_1000_, v___x_1004_, v_a_996_);
v___x_1007_ = l_Lean_Meta_Grind_closeGoal(v___x_1006_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v___x_1007_;
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec(v_a_998_);
lean_dec(v_a_996_);
lean_dec(v_a_994_);
v_a_1008_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_999_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_999_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_a_996_);
lean_dec(v_a_994_);
v_a_1016_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_997_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_997_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_a_994_);
v_a_1024_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_995_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_995_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_rhs_981_);
lean_dec_ref(v_lhs_980_);
v_a_1032_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_993_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_993_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1040_, lean_object* v_rhs_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1040_, v_rhs_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec(v_a_1042_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1054_, lean_object* v_as_x27_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
if (lean_obj_tag(v_as_x27_1055_) == 0)
{
lean_object* v___x_1068_; 
lean_dec(v___x_1054_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v_b_1056_);
return v___x_1068_;
}
else
{
lean_object* v_head_1069_; lean_object* v_tail_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_head_1069_ = lean_ctor_get(v_as_x27_1055_, 0);
v_tail_1070_ = lean_ctor_get(v_as_x27_1055_, 1);
v___x_1071_ = lean_st_ref_get(v___y_1057_);
lean_inc(v_head_1069_);
v___x_1072_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1071_, v_head_1069_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___x_1071_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v_self_1074_; lean_object* v_next_1075_; lean_object* v_root_1076_; lean_object* v_congr_1077_; lean_object* v_target_x3f_1078_; lean_object* v_proof_x3f_1079_; uint8_t v_flipped_1080_; lean_object* v_size_1081_; uint8_t v_interpreted_1082_; uint8_t v_ctor_1083_; uint8_t v_hasLambdas_1084_; uint8_t v_heqProofs_1085_; lean_object* v_idx_1086_; lean_object* v_generation_1087_; lean_object* v_mt_1088_; lean_object* v_sTerms_1089_; uint8_t v_funCC_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1103_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref(v___x_1072_);
v_self_1074_ = lean_ctor_get(v_a_1073_, 0);
v_next_1075_ = lean_ctor_get(v_a_1073_, 1);
v_root_1076_ = lean_ctor_get(v_a_1073_, 2);
v_congr_1077_ = lean_ctor_get(v_a_1073_, 3);
v_target_x3f_1078_ = lean_ctor_get(v_a_1073_, 4);
v_proof_x3f_1079_ = lean_ctor_get(v_a_1073_, 5);
v_flipped_1080_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*11);
v_size_1081_ = lean_ctor_get(v_a_1073_, 6);
v_interpreted_1082_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*11 + 1);
v_ctor_1083_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*11 + 2);
v_hasLambdas_1084_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*11 + 3);
v_heqProofs_1085_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*11 + 4);
v_idx_1086_ = lean_ctor_get(v_a_1073_, 7);
v_generation_1087_ = lean_ctor_get(v_a_1073_, 8);
v_mt_1088_ = lean_ctor_get(v_a_1073_, 9);
v_sTerms_1089_ = lean_ctor_get(v_a_1073_, 10);
v_funCC_1090_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*11 + 5);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_a_1073_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1092_ = v_a_1073_;
v_isShared_1093_ = v_isSharedCheck_1103_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_sTerms_1089_);
lean_inc(v_mt_1088_);
lean_inc(v_generation_1087_);
lean_inc(v_idx_1086_);
lean_inc(v_size_1081_);
lean_inc(v_proof_x3f_1079_);
lean_inc(v_target_x3f_1078_);
lean_inc(v_congr_1077_);
lean_inc(v_root_1076_);
lean_inc(v_next_1075_);
lean_inc(v_self_1074_);
lean_dec(v_a_1073_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1103_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_nat_dec_lt(v_mt_1088_, v___x_1054_);
lean_dec(v_mt_1088_);
if (v___x_1095_ == 0)
{
lean_del_object(v___x_1092_);
lean_dec(v_sTerms_1089_);
lean_dec(v_generation_1087_);
lean_dec(v_idx_1086_);
lean_dec(v_size_1081_);
lean_dec(v_proof_x3f_1079_);
lean_dec(v_target_x3f_1078_);
lean_dec_ref(v_congr_1077_);
lean_dec_ref(v_root_1076_);
lean_dec_ref(v_next_1075_);
lean_dec_ref(v_self_1074_);
v_as_x27_1055_ = v_tail_1070_;
v_b_1056_ = v___x_1094_;
goto _start;
}
else
{
lean_object* v___x_1098_; 
lean_inc(v___x_1054_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 9, v___x_1054_);
v___x_1098_ = v___x_1092_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_self_1074_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_next_1075_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_root_1076_);
lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_congr_1077_);
lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_target_x3f_1078_);
lean_ctor_set(v_reuseFailAlloc_1102_, 5, v_proof_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1102_, 6, v_size_1081_);
lean_ctor_set(v_reuseFailAlloc_1102_, 7, v_idx_1086_);
lean_ctor_set(v_reuseFailAlloc_1102_, 8, v_generation_1087_);
lean_ctor_set(v_reuseFailAlloc_1102_, 9, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1102_, 10, v_sTerms_1089_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*11, v_flipped_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*11 + 1, v_interpreted_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*11 + 2, v_ctor_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*11 + 3, v_hasLambdas_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*11 + 4, v_heqProofs_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*11 + 5, v_funCC_1090_);
v___x_1098_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; 
lean_inc(v_head_1069_);
v___x_1099_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1069_, v___x_1098_, v___y_1057_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref(v___x_1099_);
v___x_1100_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1069_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_dec_ref(v___x_1100_);
v_as_x27_1055_ = v_tail_1070_;
v_b_1056_ = v___x_1094_;
goto _start;
}
else
{
lean_dec(v___x_1054_);
return v___x_1100_;
}
}
else
{
lean_dec(v___x_1054_);
return v___x_1099_;
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v___x_1054_);
v_a_1104_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1072_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1072_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_st_ref_get(v_a_1113_);
v___x_1125_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_toGoalState_1126_; lean_object* v_ematch_1127_; lean_object* v_a_1128_; lean_object* v_gmt_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_toGoalState_1126_ = lean_ctor_get(v___x_1124_, 0);
lean_inc_ref(v_toGoalState_1126_);
lean_dec(v___x_1124_);
v_ematch_1127_ = lean_ctor_get(v_toGoalState_1126_, 12);
lean_inc_ref(v_ematch_1127_);
lean_dec_ref(v_toGoalState_1126_);
v_a_1128_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1128_);
lean_dec_ref(v___x_1125_);
v_gmt_1129_ = lean_ctor_get(v_ematch_1127_, 1);
lean_inc(v_gmt_1129_);
lean_dec_ref(v_ematch_1127_);
v___x_1130_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1128_);
lean_dec(v_a_1128_);
v___x_1131_ = lean_box(0);
v___x_1132_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1129_, v___x_1130_, v___x_1131_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v___x_1130_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1139_ == 0)
{
lean_object* v_unused_1140_; 
v_unused_1140_ = lean_ctor_get(v___x_1132_, 0);
lean_dec(v_unused_1140_);
v___x_1134_ = v___x_1132_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_dec(v___x_1132_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1131_);
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1131_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
return v___x_1132_;
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v___x_1124_);
v_a_1141_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1125_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1125_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_root_1149_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1162_, lean_object* v_as_x27_1163_, lean_object* v_b_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1162_, v_as_x27_1163_, v_b_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec(v_as_x27_1163_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1177_, lean_object* v_as_1178_, lean_object* v_as_x27_1179_, lean_object* v_b_1180_, lean_object* v_a_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1177_, v_as_x27_1179_, v_b_1180_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1194_, lean_object* v_as_1195_, lean_object* v_as_x27_1196_, lean_object* v_b_1197_, lean_object* v_a_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1194_, v_as_1195_, v_as_x27_1196_, v_b_1197_, v_a_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
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
lean_dec(v_as_x27_1196_);
lean_dec(v_as_1195_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
if (lean_obj_tag(v_a_1211_) == 0)
{
lean_object* v___x_1213_; 
v___x_1213_ = l_List_reverse___redArg(v_a_1212_);
return v___x_1213_;
}
else
{
lean_object* v_head_1214_; lean_object* v_tail_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1224_; 
v_head_1214_ = lean_ctor_get(v_a_1211_, 0);
v_tail_1215_ = lean_ctor_get(v_a_1211_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_a_1211_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1217_ = v_a_1211_;
v_isShared_1218_ = v_isSharedCheck_1224_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_tail_1215_);
lean_inc(v_head_1214_);
lean_dec(v_a_1211_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1224_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = l_Lean_MessageData_ofExpr(v_head_1214_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v_a_1212_);
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_a_1212_);
v___x_1221_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v_a_1211_ = v_tail_1215_;
v_a_1212_ = v___x_1221_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1231_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1232_ = l_Lean_Name_append(v___x_1231_, v___x_1230_);
return v___x_1232_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3));
v___x_1235_ = l_Lean_stringToMessageData(v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_lams_1238_, lean_object* v_b_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_fst_1251_; lean_object* v_snd_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1357_; 
v_fst_1251_ = lean_ctor_get(v_b_1239_, 0);
v_snd_1252_ = lean_ctor_get(v_b_1239_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_b_1239_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1254_ = v_b_1239_;
v_isShared_1255_ = v_isSharedCheck_1357_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_snd_1252_);
lean_inc(v_fst_1251_);
lean_dec(v_b_1239_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1357_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v_options_1330_; uint8_t v_hasTrace_1331_; 
v_options_1330_ = lean_ctor_get(v___y_1248_, 2);
v_hasTrace_1331_ = lean_ctor_get_uint8(v_options_1330_, sizeof(void*)*1);
if (v_hasTrace_1331_ == 0)
{
v___y_1299_ = v___y_1240_;
v___y_1300_ = v___y_1241_;
v___y_1301_ = v___y_1242_;
v___y_1302_ = v___y_1243_;
v___y_1303_ = v___y_1244_;
v___y_1304_ = v___y_1245_;
v___y_1305_ = v___y_1246_;
v___y_1306_ = v___y_1247_;
v___y_1307_ = v___y_1248_;
v___y_1308_ = v___y_1249_;
goto v___jp_1298_;
}
else
{
lean_object* v_inheritedTraceOptions_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v_inheritedTraceOptions_1332_ = lean_ctor_get(v___y_1248_, 13);
v___x_1333_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1334_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1335_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1332_, v_options_1330_, v___x_1334_);
if (v___x_1335_ == 0)
{
v___y_1299_ = v___y_1240_;
v___y_1300_ = v___y_1241_;
v___y_1301_ = v___y_1242_;
v___y_1302_ = v___y_1243_;
v___y_1303_ = v___y_1244_;
v___y_1304_ = v___y_1245_;
v___y_1305_ = v___y_1246_;
v___y_1306_ = v___y_1247_;
v___y_1307_ = v___y_1248_;
v___y_1308_ = v___y_1249_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Meta_Grind_updateLastTag(v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
lean_dec_ref(v___x_1336_);
v___x_1337_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4);
lean_inc(v_snd_1252_);
v___x_1338_ = l_Lean_MessageData_ofExpr(v_snd_1252_);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1333_, v___x_1339_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_dec_ref(v___x_1340_);
v___y_1299_ = v___y_1240_;
v___y_1300_ = v___y_1241_;
v___y_1301_ = v___y_1242_;
v___y_1302_ = v___y_1243_;
v___y_1303_ = v___y_1244_;
v___y_1304_ = v___y_1245_;
v___y_1305_ = v___y_1246_;
v___y_1306_ = v___y_1247_;
v___y_1307_ = v___y_1248_;
v___y_1308_ = v___y_1249_;
goto v___jp_1298_;
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_del_object(v___x_1254_);
lean_dec(v_snd_1252_);
lean_dec(v_fst_1251_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_del_object(v___x_1254_);
lean_dec(v_snd_1252_);
lean_dec(v_fst_1251_);
v_a_1349_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1336_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1336_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
v___jp_1256_:
{
if (lean_obj_tag(v_snd_1252_) == 5)
{
lean_object* v_fn_1267_; lean_object* v_arg_1268_; lean_object* v___x_1269_; 
v_fn_1267_ = lean_ctor_get(v_snd_1252_, 0);
lean_inc_ref(v_fn_1267_);
v_arg_1268_ = lean_ctor_get(v_snd_1252_, 1);
lean_inc_ref(v_arg_1268_);
v___x_1269_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1236_, v___y_1257_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
v___x_1271_ = lean_box(0);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v___y_1258_);
lean_inc(v___y_1257_);
v___x_1272_ = lean_grind_internalize(v_snd_1252_, v_a_1270_, v___x_1271_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
lean_dec_ref(v___x_1272_);
v___x_1273_ = lean_array_push(v_fst_1251_, v_arg_1268_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v_fn_1267_);
lean_ctor_set(v___x_1254_, 0, v___x_1273_);
v___x_1275_ = v___x_1254_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_fn_1267_);
v___x_1275_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
v_b_1239_ = v___x_1275_;
goto _start;
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_arg_1268_);
lean_dec_ref(v_fn_1267_);
lean_del_object(v___x_1254_);
lean_dec(v_fst_1251_);
v_a_1278_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1272_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1272_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_arg_1268_);
lean_dec_ref(v_fn_1267_);
lean_dec_ref(v_snd_1252_);
lean_del_object(v___x_1254_);
lean_dec(v_fst_1251_);
v_a_1286_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1269_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1269_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v___x_1295_; 
if (v_isShared_1255_ == 0)
{
v___x_1295_ = v___x_1254_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_fst_1251_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_snd_1252_);
v___x_1295_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
return v___x_1296_;
}
}
}
v___jp_1298_:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1252_, v_a_1237_, v___y_1299_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; uint8_t v___x_1311_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1309_);
v___x_1311_ = lean_unbox(v_a_1310_);
lean_dec(v_a_1310_);
if (v___x_1311_ == 0)
{
v___y_1257_ = v___y_1299_;
v___y_1258_ = v___y_1300_;
v___y_1259_ = v___y_1301_;
v___y_1260_ = v___y_1302_;
v___y_1261_ = v___y_1303_;
v___y_1262_ = v___y_1304_;
v___y_1263_ = v___y_1305_;
v___y_1264_ = v___y_1306_;
v___y_1265_ = v___y_1307_;
v___y_1266_ = v___y_1308_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_inc(v_fst_1251_);
v___x_1312_ = l_Array_reverse___redArg(v_fst_1251_);
lean_inc(v_snd_1252_);
v___x_1313_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1238_, v_snd_1252_, v___x_1312_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_dec_ref(v___x_1313_);
v___y_1257_ = v___y_1299_;
v___y_1258_ = v___y_1300_;
v___y_1259_ = v___y_1301_;
v___y_1260_ = v___y_1302_;
v___y_1261_ = v___y_1303_;
v___y_1262_ = v___y_1304_;
v___y_1263_ = v___y_1305_;
v___y_1264_ = v___y_1306_;
v___y_1265_ = v___y_1307_;
v___y_1266_ = v___y_1308_;
goto v___jp_1256_;
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_del_object(v___x_1254_);
lean_dec(v_snd_1252_);
lean_dec(v_fst_1251_);
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_del_object(v___x_1254_);
lean_dec(v_snd_1252_);
lean_dec(v_fst_1251_);
v_a_1322_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1309_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1309_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_lams_1360_, lean_object* v_b_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1358_, v_a_1359_, v_lams_1360_, v_b_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v_lams_1360_);
lean_dec_ref(v_a_1359_);
lean_dec_ref(v_a_1358_);
return v_res_1373_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1379_, lean_object* v_lams_1380_, lean_object* v_as_x27_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
if (lean_obj_tag(v_as_x27_1381_) == 0)
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v_b_1382_);
return v___x_1394_;
}
else
{
lean_object* v_options_1395_; lean_object* v_head_1396_; lean_object* v_tail_1397_; lean_object* v_inheritedTraceOptions_1398_; uint8_t v_hasTrace_1399_; lean_object* v___x_1400_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___x_1424_; uint8_t v_a_1426_; 
v_options_1395_ = lean_ctor_get(v___y_1391_, 2);
v_head_1396_ = lean_ctor_get(v_as_x27_1381_, 0);
v_tail_1397_ = lean_ctor_get(v_as_x27_1381_, 1);
v_inheritedTraceOptions_1398_ = lean_ctor_get(v___y_1391_, 13);
v_hasTrace_1399_ = lean_ctor_get_uint8(v_options_1395_, sizeof(void*)*1);
v___x_1400_ = lean_box(0);
v___x_1424_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
if (v_hasTrace_1399_ == 0)
{
v_a_1426_ = v_hasTrace_1399_;
goto v___jp_1425_;
}
else
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1434_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1398_, v_options_1395_, v___x_1433_);
v_a_1426_ = v___x_1434_;
goto v___jp_1425_;
}
v___jp_1401_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
lean_inc(v_head_1396_);
lean_inc_ref(v___y_1402_);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___y_1402_);
lean_ctor_set(v___x_1413_, 1, v_head_1396_);
v___x_1414_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_head_1396_, v_a_1379_, v_lams_1380_, v___x_1413_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_dec_ref(v___x_1414_);
v_as_x27_1381_ = v_tail_1397_;
v_b_1382_ = v___x_1400_;
goto _start;
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_a_1416_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1414_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1414_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
v___jp_1425_:
{
lean_object* v___x_1427_; 
v___x_1427_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1426_ == 0)
{
v___y_1402_ = v___x_1427_;
v___y_1403_ = v___y_1383_;
v___y_1404_ = v___y_1384_;
v___y_1405_ = v___y_1385_;
v___y_1406_ = v___y_1386_;
v___y_1407_ = v___y_1387_;
v___y_1408_ = v___y_1388_;
v___y_1409_ = v___y_1389_;
v___y_1410_ = v___y_1390_;
v___y_1411_ = v___y_1391_;
v___y_1412_ = v___y_1392_;
goto v___jp_1401_;
}
else
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Meta_Grind_updateLastTag(v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v___x_1428_);
v___x_1429_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1396_);
v___x_1430_ = l_Lean_MessageData_ofExpr(v_head_1396_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1424_, v___x_1431_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_dec_ref(v___x_1432_);
v___y_1402_ = v___x_1427_;
v___y_1403_ = v___y_1383_;
v___y_1404_ = v___y_1384_;
v___y_1405_ = v___y_1385_;
v___y_1406_ = v___y_1386_;
v___y_1407_ = v___y_1387_;
v___y_1408_ = v___y_1388_;
v___y_1409_ = v___y_1389_;
v___y_1410_ = v___y_1390_;
v___y_1411_ = v___y_1391_;
v___y_1412_ = v___y_1392_;
goto v___jp_1401_;
}
else
{
return v___x_1432_;
}
}
else
{
return v___x_1428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1435_, lean_object* v_lams_1436_, lean_object* v_as_x27_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1435_, v_lams_1436_, v_as_x27_1437_, v_b_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec(v_as_x27_1437_);
lean_dec_ref(v_lams_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1451_, lean_object* v_lams_1452_, lean_object* v_as_1453_, lean_object* v_as_x27_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
if (lean_obj_tag(v_as_x27_1454_) == 0)
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_b_1455_);
return v___x_1467_;
}
else
{
lean_object* v_options_1468_; lean_object* v_head_1469_; lean_object* v_tail_1470_; lean_object* v_inheritedTraceOptions_1471_; uint8_t v_hasTrace_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; uint8_t v_a_1499_; 
v_options_1468_ = lean_ctor_get(v___y_1464_, 2);
v_head_1469_ = lean_ctor_get(v_as_x27_1454_, 0);
v_tail_1470_ = lean_ctor_get(v_as_x27_1454_, 1);
v_inheritedTraceOptions_1471_ = lean_ctor_get(v___y_1464_, 13);
v_hasTrace_1472_ = lean_ctor_get_uint8(v_options_1468_, sizeof(void*)*1);
v___x_1473_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1474_ = lean_box(0);
if (v_hasTrace_1472_ == 0)
{
v_a_1499_ = v_hasTrace_1472_;
goto v___jp_1498_;
}
else
{
lean_object* v___x_1506_; uint8_t v___x_1507_; 
v___x_1506_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1507_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1471_, v_options_1468_, v___x_1506_);
v_a_1499_ = v___x_1507_;
goto v___jp_1498_;
}
v___jp_1475_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_inc(v_head_1469_);
lean_inc_ref(v___y_1476_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___y_1476_);
lean_ctor_set(v___x_1487_, 1, v_head_1469_);
v___x_1488_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_head_1469_, v_a_1451_, v_lams_1452_, v___x_1487_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1489_; 
lean_dec_ref(v___x_1488_);
v___x_1489_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1451_, v_lams_1452_, v_tail_1470_, v___x_1474_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1489_;
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
v_a_1490_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1488_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1488_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
v___jp_1498_:
{
lean_object* v___x_1500_; 
v___x_1500_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1499_ == 0)
{
v___y_1476_ = v___x_1500_;
v___y_1477_ = v___y_1456_;
v___y_1478_ = v___y_1457_;
v___y_1479_ = v___y_1458_;
v___y_1480_ = v___y_1459_;
v___y_1481_ = v___y_1460_;
v___y_1482_ = v___y_1461_;
v___y_1483_ = v___y_1462_;
v___y_1484_ = v___y_1463_;
v___y_1485_ = v___y_1464_;
v___y_1486_ = v___y_1465_;
goto v___jp_1475_;
}
else
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Meta_Grind_updateLastTag(v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v___x_1501_);
v___x_1502_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1469_);
v___x_1503_ = l_Lean_MessageData_ofExpr(v_head_1469_);
v___x_1504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1473_, v___x_1504_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_dec_ref(v___x_1505_);
v___y_1476_ = v___x_1500_;
v___y_1477_ = v___y_1456_;
v___y_1478_ = v___y_1457_;
v___y_1479_ = v___y_1458_;
v___y_1480_ = v___y_1459_;
v___y_1481_ = v___y_1460_;
v___y_1482_ = v___y_1461_;
v___y_1483_ = v___y_1462_;
v___y_1484_ = v___y_1463_;
v___y_1485_ = v___y_1464_;
v___y_1486_ = v___y_1465_;
goto v___jp_1475_;
}
else
{
return v___x_1505_;
}
}
else
{
return v___x_1501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1508_, lean_object* v_lams_1509_, lean_object* v_as_1510_, lean_object* v_as_x27_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1508_, v_lams_1509_, v_as_1510_, v_as_x27_1511_, v_b_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec(v_as_x27_1511_);
lean_dec(v_as_1510_);
lean_dec_ref(v_lams_1509_);
lean_dec_ref(v_a_1508_);
return v_res_1524_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1531_, lean_object* v_lams_1532_, lean_object* v_as_1533_, size_t v_sz_1534_, size_t v_i_1535_, lean_object* v_b_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v___x_1548_; 
v___x_1548_ = lean_usize_dec_lt(v_i_1535_, v_sz_1534_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_b_1536_);
return v___x_1549_;
}
else
{
lean_object* v_options_1550_; lean_object* v_inheritedTraceOptions_1551_; uint8_t v_hasTrace_1552_; lean_object* v___x_1553_; lean_object* v_a_1554_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; 
v_options_1550_ = lean_ctor_get(v___y_1545_, 2);
v_inheritedTraceOptions_1551_ = lean_ctor_get(v___y_1545_, 13);
v_hasTrace_1552_ = lean_ctor_get_uint8(v_options_1550_, sizeof(void*)*1);
v___x_1553_ = lean_box(0);
v_a_1554_ = lean_array_uget_borrowed(v_as_1533_, v_i_1535_);
if (v_hasTrace_1552_ == 0)
{
v___y_1556_ = v___y_1537_;
v___y_1557_ = v___y_1538_;
v___y_1558_ = v___y_1539_;
v___y_1559_ = v___y_1540_;
v___y_1560_ = v___y_1541_;
v___y_1561_ = v___y_1542_;
v___y_1562_ = v___y_1543_;
v___y_1563_ = v___y_1544_;
v___y_1564_ = v___y_1545_;
v___y_1565_ = v___y_1546_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1581_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1582_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1583_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1551_, v_options_1550_, v___x_1582_);
if (v___x_1583_ == 0)
{
v___y_1556_ = v___y_1537_;
v___y_1557_ = v___y_1538_;
v___y_1558_ = v___y_1539_;
v___y_1559_ = v___y_1540_;
v___y_1560_ = v___y_1541_;
v___y_1561_ = v___y_1542_;
v___y_1562_ = v___y_1543_;
v___y_1563_ = v___y_1544_;
v___y_1564_ = v___y_1545_;
v___y_1565_ = v___y_1546_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Meta_Grind_updateLastTag(v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref(v___x_1584_);
v___x_1585_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1554_, v___y_1537_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1585_);
v___x_1587_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1554_);
v___x_1588_ = l_Lean_MessageData_ofExpr(v_a_1554_);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1586_);
lean_dec(v_a_1586_);
v___x_1593_ = lean_box(0);
v___x_1594_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1592_, v___x_1593_);
v___x_1595_ = l_Lean_MessageData_ofList(v___x_1594_);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1591_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1581_, v___x_1596_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_dec_ref(v___x_1597_);
v___y_1556_ = v___y_1537_;
v___y_1557_ = v___y_1538_;
v___y_1558_ = v___y_1539_;
v___y_1559_ = v___y_1540_;
v___y_1560_ = v___y_1541_;
v___y_1561_ = v___y_1542_;
v___y_1562_ = v___y_1543_;
v___y_1563_ = v___y_1544_;
v___y_1564_ = v___y_1545_;
v___y_1565_ = v___y_1546_;
goto v___jp_1555_;
}
else
{
return v___x_1597_;
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_a_1598_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1585_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1585_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
else
{
return v___x_1584_;
}
}
}
v___jp_1555_:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1554_, v___y_1556_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1566_);
v___x_1568_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1567_);
lean_dec(v_a_1567_);
v___x_1569_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1531_, v_lams_1532_, v___x_1568_, v___x_1568_, v___x_1553_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___x_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
size_t v___x_1570_; size_t v___x_1571_; 
lean_dec_ref(v___x_1569_);
v___x_1570_ = ((size_t)1ULL);
v___x_1571_ = lean_usize_add(v_i_1535_, v___x_1570_);
v_i_1535_ = v___x_1571_;
v_b_1536_ = v___x_1553_;
goto _start;
}
else
{
return v___x_1569_;
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v_a_1573_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1566_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1566_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1606_ = _args[0];
lean_object* v_lams_1607_ = _args[1];
lean_object* v_as_1608_ = _args[2];
lean_object* v_sz_1609_ = _args[3];
lean_object* v_i_1610_ = _args[4];
lean_object* v_b_1611_ = _args[5];
lean_object* v___y_1612_ = _args[6];
lean_object* v___y_1613_ = _args[7];
lean_object* v___y_1614_ = _args[8];
lean_object* v___y_1615_ = _args[9];
lean_object* v___y_1616_ = _args[10];
lean_object* v___y_1617_ = _args[11];
lean_object* v___y_1618_ = _args[12];
lean_object* v___y_1619_ = _args[13];
lean_object* v___y_1620_ = _args[14];
lean_object* v___y_1621_ = _args[15];
lean_object* v___y_1622_ = _args[16];
_start:
{
size_t v_sz_boxed_1623_; size_t v_i_boxed_1624_; lean_object* v_res_1625_; 
v_sz_boxed_1623_ = lean_unbox_usize(v_sz_1609_);
lean_dec(v_sz_1609_);
v_i_boxed_1624_ = lean_unbox_usize(v_i_1610_);
lean_dec(v_i_1610_);
v_res_1625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1606_, v_lams_1607_, v_as_1608_, v_sz_boxed_1623_, v_i_boxed_1624_, v_b_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v_as_1608_);
lean_dec_ref(v_lams_1607_);
lean_dec_ref(v_a_1606_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1626_, lean_object* v_lams_1627_, lean_object* v_as_1628_, size_t v_sz_1629_, size_t v_i_1630_, lean_object* v_b_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
uint8_t v___x_1643_; 
v___x_1643_ = lean_usize_dec_lt(v_i_1630_, v_sz_1629_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v_b_1631_);
return v___x_1644_;
}
else
{
lean_object* v_options_1645_; lean_object* v_inheritedTraceOptions_1646_; uint8_t v_hasTrace_1647_; lean_object* v___x_1648_; lean_object* v_a_1649_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; 
v_options_1645_ = lean_ctor_get(v___y_1640_, 2);
v_inheritedTraceOptions_1646_ = lean_ctor_get(v___y_1640_, 13);
v_hasTrace_1647_ = lean_ctor_get_uint8(v_options_1645_, sizeof(void*)*1);
v___x_1648_ = lean_box(0);
v_a_1649_ = lean_array_uget_borrowed(v_as_1628_, v_i_1630_);
if (v_hasTrace_1647_ == 0)
{
v___y_1651_ = v___y_1632_;
v___y_1652_ = v___y_1633_;
v___y_1653_ = v___y_1634_;
v___y_1654_ = v___y_1635_;
v___y_1655_ = v___y_1636_;
v___y_1656_ = v___y_1637_;
v___y_1657_ = v___y_1638_;
v___y_1658_ = v___y_1639_;
v___y_1659_ = v___y_1640_;
v___y_1660_ = v___y_1641_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1676_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1677_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1646_, v_options_1645_, v___x_1677_);
if (v___x_1678_ == 0)
{
v___y_1651_ = v___y_1632_;
v___y_1652_ = v___y_1633_;
v___y_1653_ = v___y_1634_;
v___y_1654_ = v___y_1635_;
v___y_1655_ = v___y_1636_;
v___y_1656_ = v___y_1637_;
v___y_1657_ = v___y_1638_;
v___y_1658_ = v___y_1639_;
v___y_1659_ = v___y_1640_;
v___y_1660_ = v___y_1641_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Meta_Grind_updateLastTag(v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v___x_1680_; 
lean_dec_ref(v___x_1679_);
v___x_1680_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1649_, v___y_1632_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1649_);
v___x_1683_ = l_Lean_MessageData_ofExpr(v_a_1649_);
v___x_1684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1681_);
lean_dec(v_a_1681_);
v___x_1688_ = lean_box(0);
v___x_1689_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1687_, v___x_1688_);
v___x_1690_ = l_Lean_MessageData_ofList(v___x_1689_);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1686_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1676_, v___x_1691_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_dec_ref(v___x_1692_);
v___y_1651_ = v___y_1632_;
v___y_1652_ = v___y_1633_;
v___y_1653_ = v___y_1634_;
v___y_1654_ = v___y_1635_;
v___y_1655_ = v___y_1636_;
v___y_1656_ = v___y_1637_;
v___y_1657_ = v___y_1638_;
v___y_1658_ = v___y_1639_;
v___y_1659_ = v___y_1640_;
v___y_1660_ = v___y_1641_;
goto v___jp_1650_;
}
else
{
return v___x_1692_;
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
v_a_1693_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1680_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1680_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
return v___x_1679_;
}
}
}
v___jp_1650_:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1649_, v___y_1651_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1662_);
lean_dec(v_a_1662_);
v___x_1664_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1626_, v_lams_1627_, v___x_1663_, v___x_1663_, v___x_1648_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___x_1663_);
if (lean_obj_tag(v___x_1664_) == 0)
{
size_t v___x_1665_; size_t v___x_1666_; lean_object* v___x_1667_; 
lean_dec_ref(v___x_1664_);
v___x_1665_ = ((size_t)1ULL);
v___x_1666_ = lean_usize_add(v_i_1630_, v___x_1665_);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1626_, v_lams_1627_, v_as_1628_, v_sz_1629_, v___x_1666_, v___x_1648_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v___x_1667_;
}
else
{
return v___x_1664_;
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1661_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1661_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1701_ = _args[0];
lean_object* v_lams_1702_ = _args[1];
lean_object* v_as_1703_ = _args[2];
lean_object* v_sz_1704_ = _args[3];
lean_object* v_i_1705_ = _args[4];
lean_object* v_b_1706_ = _args[5];
lean_object* v___y_1707_ = _args[6];
lean_object* v___y_1708_ = _args[7];
lean_object* v___y_1709_ = _args[8];
lean_object* v___y_1710_ = _args[9];
lean_object* v___y_1711_ = _args[10];
lean_object* v___y_1712_ = _args[11];
lean_object* v___y_1713_ = _args[12];
lean_object* v___y_1714_ = _args[13];
lean_object* v___y_1715_ = _args[14];
lean_object* v___y_1716_ = _args[15];
lean_object* v___y_1717_ = _args[16];
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1704_);
lean_dec(v_sz_1704_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1705_);
lean_dec(v_i_1705_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1701_, v_lams_1702_, v_as_1703_, v_sz_boxed_1718_, v_i_boxed_1719_, v_b_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v_as_1703_);
lean_dec_ref(v_lams_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1720_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1726_ = l_Lean_stringToMessageData(v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1727_, lean_object* v_fns_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1740_ = lean_array_get_size(v_lams_1727_);
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_nat_dec_eq(v___x_1740_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1743_ = lean_st_ref_get(v_a_1729_);
v___x_1744_ = l_Lean_instInhabitedExpr;
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_nat_sub(v___x_1740_, v___x_1745_);
v___x_1747_ = lean_array_get_borrowed(v___x_1744_, v_lams_1727_, v___x_1746_);
lean_dec(v___x_1746_);
lean_inc(v___x_1747_);
v___x_1748_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1743_, v___x_1747_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_);
lean_dec(v___x_1743_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v_options_1773_; uint8_t v_hasTrace_1774_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref(v___x_1748_);
v_options_1773_ = lean_ctor_get(v_a_1737_, 2);
v_hasTrace_1774_ = lean_ctor_get_uint8(v_options_1773_, sizeof(void*)*1);
if (v_hasTrace_1774_ == 0)
{
v___y_1751_ = v_a_1729_;
v___y_1752_ = v_a_1730_;
v___y_1753_ = v_a_1731_;
v___y_1754_ = v_a_1732_;
v___y_1755_ = v_a_1733_;
v___y_1756_ = v_a_1734_;
v___y_1757_ = v_a_1735_;
v___y_1758_ = v_a_1736_;
v___y_1759_ = v_a_1737_;
v___y_1760_ = v_a_1738_;
goto v___jp_1750_;
}
else
{
lean_object* v_inheritedTraceOptions_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_inheritedTraceOptions_1775_ = lean_ctor_get(v_a_1737_, 13);
v___x_1776_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1777_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1778_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1775_, v_options_1773_, v___x_1777_);
if (v___x_1778_ == 0)
{
v___y_1751_ = v_a_1729_;
v___y_1752_ = v_a_1730_;
v___y_1753_ = v_a_1731_;
v___y_1754_ = v_a_1732_;
v___y_1755_ = v_a_1733_;
v___y_1756_ = v_a_1734_;
v___y_1757_ = v_a_1735_;
v___y_1758_ = v_a_1736_;
v___y_1759_ = v_a_1737_;
v___y_1760_ = v_a_1738_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Meta_Grind_updateLastTag(v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec_ref(v___x_1779_);
v___x_1780_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1728_);
v___x_1781_ = lean_array_to_list(v_fns_1728_);
v___x_1782_ = lean_box(0);
v___x_1783_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1781_, v___x_1782_);
v___x_1784_ = l_Lean_MessageData_ofList(v___x_1783_);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1780_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
lean_inc_ref(v_lams_1727_);
v___x_1788_ = lean_array_to_list(v_lams_1727_);
v___x_1789_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1788_, v___x_1782_);
v___x_1790_ = l_Lean_MessageData_ofList(v___x_1789_);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1787_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1776_, v___x_1791_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_dec_ref(v___x_1792_);
v___y_1751_ = v_a_1729_;
v___y_1752_ = v_a_1730_;
v___y_1753_ = v_a_1731_;
v___y_1754_ = v_a_1732_;
v___y_1755_ = v_a_1733_;
v___y_1756_ = v_a_1734_;
v___y_1757_ = v_a_1735_;
v___y_1758_ = v_a_1736_;
v___y_1759_ = v_a_1737_;
v___y_1760_ = v_a_1738_;
goto v___jp_1750_;
}
else
{
lean_dec(v_a_1749_);
lean_dec_ref(v_fns_1728_);
lean_dec_ref(v_lams_1727_);
return v___x_1792_;
}
}
else
{
lean_dec(v_a_1749_);
lean_dec_ref(v_fns_1728_);
lean_dec_ref(v_lams_1727_);
return v___x_1779_;
}
}
}
v___jp_1750_:
{
lean_object* v___x_1761_; size_t v_sz_1762_; size_t v___x_1763_; lean_object* v___x_1764_; 
v___x_1761_ = lean_box(0);
v_sz_1762_ = lean_array_size(v_fns_1728_);
v___x_1763_ = ((size_t)0ULL);
v___x_1764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1749_, v_lams_1727_, v_fns_1728_, v_sz_1762_, v___x_1763_, v___x_1761_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec_ref(v_fns_1728_);
lean_dec_ref(v_lams_1727_);
lean_dec(v_a_1749_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v___x_1764_, 0);
lean_dec(v_unused_1772_);
v___x_1766_ = v___x_1764_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_dec(v___x_1764_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1761_);
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1761_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
else
{
return v___x_1764_;
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v_fns_1728_);
lean_dec_ref(v_lams_1727_);
v_a_1793_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1748_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1748_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec_ref(v_fns_1728_);
lean_dec_ref(v_lams_1727_);
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
return v___x_1802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1803_, lean_object* v_fns_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1803_, v_fns_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec(v_a_1805_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1817_, lean_object* v_lams_1818_, lean_object* v_as_1819_, lean_object* v_as_x27_1820_, lean_object* v_b_1821_, lean_object* v_a_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1817_, v_lams_1818_, v_as_1819_, v_as_x27_1820_, v_b_1821_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1835_ = _args[0];
lean_object* v_lams_1836_ = _args[1];
lean_object* v_as_1837_ = _args[2];
lean_object* v_as_x27_1838_ = _args[3];
lean_object* v_b_1839_ = _args[4];
lean_object* v_a_1840_ = _args[5];
lean_object* v___y_1841_ = _args[6];
lean_object* v___y_1842_ = _args[7];
lean_object* v___y_1843_ = _args[8];
lean_object* v___y_1844_ = _args[9];
lean_object* v___y_1845_ = _args[10];
lean_object* v___y_1846_ = _args[11];
lean_object* v___y_1847_ = _args[12];
lean_object* v___y_1848_ = _args[13];
lean_object* v___y_1849_ = _args[14];
lean_object* v___y_1850_ = _args[15];
lean_object* v___y_1851_ = _args[16];
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1835_, v_lams_1836_, v_as_1837_, v_as_x27_1838_, v_b_1839_, v_a_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec(v_as_x27_1838_);
lean_dec(v_as_1837_);
lean_dec_ref(v_lams_1836_);
lean_dec_ref(v_a_1835_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1853_, lean_object* v_lams_1854_, lean_object* v_as_1855_, lean_object* v_as_x27_1856_, lean_object* v_b_1857_, lean_object* v_a_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1853_, v_lams_1854_, v_as_x27_1856_, v_b_1857_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1871_ = _args[0];
lean_object* v_lams_1872_ = _args[1];
lean_object* v_as_1873_ = _args[2];
lean_object* v_as_x27_1874_ = _args[3];
lean_object* v_b_1875_ = _args[4];
lean_object* v_a_1876_ = _args[5];
lean_object* v___y_1877_ = _args[6];
lean_object* v___y_1878_ = _args[7];
lean_object* v___y_1879_ = _args[8];
lean_object* v___y_1880_ = _args[9];
lean_object* v___y_1881_ = _args[10];
lean_object* v___y_1882_ = _args[11];
lean_object* v___y_1883_ = _args[12];
lean_object* v___y_1884_ = _args[13];
lean_object* v___y_1885_ = _args[14];
lean_object* v___y_1886_ = _args[15];
lean_object* v___y_1887_ = _args[16];
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1871_, v_lams_1872_, v_as_1873_, v_as_x27_1874_, v_b_1875_, v_a_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec(v_as_x27_1874_);
lean_dec(v_as_1873_);
lean_dec_ref(v_lams_1872_);
lean_dec_ref(v_a_1871_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1892_, lean_object* v_as_1893_, size_t v_sz_1894_, size_t v_i_1895_, lean_object* v_b_1896_){
_start:
{
lean_object* v_a_1898_; uint8_t v___x_1902_; 
v___x_1902_ = lean_usize_dec_lt(v_i_1895_, v_sz_1894_);
if (v___x_1902_ == 0)
{
lean_inc_ref(v_b_1896_);
return v_b_1896_;
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_a_1905_; 
v___x_1903_ = lean_box(0);
v___x_1904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1905_ = lean_array_uget_borrowed(v_as_1893_, v_i_1895_);
if (lean_obj_tag(v_a_1905_) == 6)
{
lean_object* v_binderType_1906_; uint8_t v___x_1907_; 
v_binderType_1906_ = lean_ctor_get(v_a_1905_, 1);
v___x_1907_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_d_1892_, v_binderType_1906_);
if (v___x_1907_ == 0)
{
v_a_1898_ = v___x_1904_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
lean_inc_ref(v_a_1905_);
v___x_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1908_, 0, v_a_1905_);
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v___x_1903_);
return v___x_1910_;
}
}
else
{
v_a_1898_ = v___x_1904_;
goto v___jp_1897_;
}
}
v___jp_1897_:
{
size_t v___x_1899_; size_t v___x_1900_; 
v___x_1899_ = ((size_t)1ULL);
v___x_1900_ = lean_usize_add(v_i_1895_, v___x_1899_);
v_i_1895_ = v___x_1900_;
v_b_1896_ = v_a_1898_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_1911_, lean_object* v_as_1912_, lean_object* v_sz_1913_, lean_object* v_i_1914_, lean_object* v_b_1915_){
_start:
{
size_t v_sz_boxed_1916_; size_t v_i_boxed_1917_; lean_object* v_res_1918_; 
v_sz_boxed_1916_ = lean_unbox_usize(v_sz_1913_);
lean_dec(v_sz_1913_);
v_i_boxed_1917_ = lean_unbox_usize(v_i_1914_);
lean_dec(v_i_1914_);
v_res_1918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1911_, v_as_1912_, v_sz_boxed_1916_, v_i_boxed_1917_, v_b_1915_);
lean_dec_ref(v_b_1915_);
lean_dec_ref(v_as_1912_);
lean_dec_ref(v_d_1911_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_1919_, lean_object* v_d_1920_){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; size_t v_sz_1923_; size_t v___x_1924_; lean_object* v___x_1925_; lean_object* v_fst_1926_; 
v___x_1921_ = lean_box(0);
v___x_1922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_1923_ = lean_array_size(v_lams_1919_);
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1920_, v_lams_1919_, v_sz_1923_, v___x_1924_, v___x_1922_);
v_fst_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_fst_1926_);
lean_dec_ref(v___x_1925_);
if (lean_obj_tag(v_fst_1926_) == 0)
{
return v___x_1921_;
}
else
{
lean_object* v_val_1927_; 
v_val_1927_ = lean_ctor_get(v_fst_1926_, 0);
lean_inc(v_val_1927_);
lean_dec_ref(v_fst_1926_);
return v_val_1927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_1928_, lean_object* v_d_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_1928_, v_d_1929_);
lean_dec_ref(v_d_1929_);
lean_dec_ref(v_lams_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_1941_, lean_object* v_lams_u2081_1942_, lean_object* v_as_1943_, size_t v_sz_1944_, size_t v_i_1945_, lean_object* v_b_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_a_1959_; uint8_t v___x_1963_; 
v___x_1963_ = lean_usize_dec_lt(v_i_1945_, v_sz_1944_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v_b_1946_);
return v___x_1964_;
}
else
{
lean_object* v___x_1965_; lean_object* v_a_1966_; 
v___x_1965_ = lean_box(0);
v_a_1966_ = lean_array_uget_borrowed(v_as_1943_, v_i_1945_);
if (lean_obj_tag(v_a_1966_) == 6)
{
lean_object* v_binderType_1967_; lean_object* v_body_1968_; lean_object* v___x_1969_; 
v_binderType_1967_ = lean_ctor_get(v_a_1966_, 1);
v_body_1968_ = lean_ctor_get(v_a_1966_, 2);
lean_inc_ref(v_binderType_1967_);
v___x_1969_ = l_Lean_Meta_getLevel(v_binderType_1967_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref(v___x_1969_);
v___x_1971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_a_1970_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
lean_inc_ref(v___x_1973_);
v___x_1974_ = l_Lean_mkConst(v___x_1971_, v___x_1973_);
lean_inc_ref(v_binderType_1967_);
v___x_1975_ = l_Lean_Expr_app___override(v___x_1974_, v_binderType_1967_);
v___x_1976_ = lean_box(0);
v___x_1977_ = l_Lean_Meta_synthInstance_x3f(v___x_1975_, v___x_1976_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1977_);
if (lean_obj_tag(v_a_1978_) == 1)
{
lean_object* v_val_1979_; lean_object* v___x_1980_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; uint8_t v___x_2045_; 
v_val_1979_ = lean_ctor_get(v_a_1978_, 0);
lean_inc(v_val_1979_);
lean_dec_ref(v_a_1978_);
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_2045_ = l_Lean_Expr_hasLooseBVars(v_body_1968_);
if (v___x_2045_ == 0)
{
v___y_1982_ = v___y_1947_;
v___y_1983_ = v___y_1948_;
v___y_1984_ = v___y_1949_;
v___y_1985_ = v___y_1950_;
v___y_1986_ = v___y_1951_;
v___y_1987_ = v___y_1952_;
v___y_1988_ = v___y_1953_;
v___y_1989_ = v___y_1954_;
v___y_1990_ = v___y_1955_;
v___y_1991_ = v___y_1956_;
goto v___jp_1981_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_1973_);
v___x_2047_ = l_Lean_mkConst(v___x_2046_, v___x_1973_);
lean_inc_ref(v_binderType_1967_);
v___x_2048_ = l_Lean_Expr_app___override(v___x_2047_, v_binderType_1967_);
v___x_2049_ = l_Lean_Meta_synthInstance_x3f(v___x_2048_, v___x_1976_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
if (lean_obj_tag(v_a_2050_) == 0)
{
lean_dec(v_val_1979_);
lean_dec_ref(v___x_1973_);
v_a_1959_ = v___x_1965_;
goto v___jp_1958_;
}
else
{
lean_dec_ref(v_a_2050_);
if (v___x_2045_ == 0)
{
lean_dec(v_val_1979_);
lean_dec_ref(v___x_1973_);
v_a_1959_ = v___x_1965_;
goto v___jp_1958_;
}
else
{
v___y_1982_ = v___y_1947_;
v___y_1983_ = v___y_1948_;
v___y_1984_ = v___y_1949_;
v___y_1985_ = v___y_1950_;
v___y_1986_ = v___y_1951_;
v___y_1987_ = v___y_1952_;
v___y_1988_ = v___y_1953_;
v___y_1989_ = v___y_1954_;
v___y_1990_ = v___y_1955_;
v___y_1991_ = v___y_1956_;
goto v___jp_1981_;
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_val_1979_);
lean_dec_ref(v___x_1973_);
v_a_2051_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2049_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2049_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
v___jp_1981_:
{
lean_object* v___x_1992_; 
v___x_1992_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_1941_, v_binderType_1967_);
if (lean_obj_tag(v___x_1992_) == 1)
{
lean_object* v_val_1993_; 
v_val_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_val_1993_);
lean_dec_ref(v___x_1992_);
if (lean_obj_tag(v_val_1993_) == 6)
{
lean_object* v_binderType_1994_; lean_object* v_body_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v_binderType_1994_ = lean_ctor_get(v_val_1993_, 1);
lean_inc_ref(v_binderType_1994_);
v_body_1995_ = lean_ctor_get(v_val_1993_, 2);
lean_inc_ref(v_body_1995_);
lean_dec_ref(v_val_1993_);
v___x_1996_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_1997_ = l_Lean_mkConst(v___x_1996_, v___x_1973_);
v___x_1998_ = l_Lean_mkAppB(v___x_1997_, v_binderType_1994_, v_val_1979_);
v___x_1999_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_1998_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref(v___x_1999_);
v___x_2001_ = lean_array_fget_borrowed(v_lams_u2081_1942_, v___x_1980_);
v___x_2002_ = lean_array_fget_borrowed(v_lams_u2082_1941_, v___x_1980_);
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
lean_inc(v___y_1985_);
lean_inc_ref(v___y_1984_);
lean_inc(v___y_1983_);
lean_inc(v___y_1982_);
lean_inc(v___x_2002_);
lean_inc(v___x_2001_);
v___x_2003_ = lean_grind_mk_eq_proof(v___x_2001_, v___x_2002_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref(v___x_2003_);
v___x_2005_ = lean_expr_instantiate1(v_body_1968_, v_a_2000_);
v___x_2006_ = lean_expr_instantiate1(v_body_1995_, v_a_2000_);
lean_dec_ref(v_body_1995_);
v___x_2007_ = l_Lean_Meta_mkCongrFun(v_a_2004_, v_a_2000_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_2007_);
v___x_2009_ = l_Lean_Meta_mkEq(v___x_2005_, v___x_2006_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = l_Lean_Meta_mkExpectedPropHint(v_a_2008_, v_a_2010_);
v___x_2012_ = l_Lean_Meta_Grind_pushNewFact(v___x_2011_, v___x_1980_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_dec_ref(v___x_2012_);
v_a_1959_ = v___x_1965_;
goto v___jp_1958_;
}
else
{
return v___x_2012_;
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_a_2008_);
v_a_2013_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2009_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2009_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec_ref(v___x_2006_);
lean_dec_ref(v___x_2005_);
v_a_2021_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2007_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2007_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_a_2000_);
lean_dec_ref(v_body_1995_);
v_a_2029_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2003_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2003_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref(v_body_1995_);
v_a_2037_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1999_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_1999_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_dec(v_val_1993_);
lean_dec(v_val_1979_);
lean_dec_ref(v___x_1973_);
v_a_1959_ = v___x_1965_;
goto v___jp_1958_;
}
}
else
{
lean_dec(v___x_1992_);
lean_dec(v_val_1979_);
lean_dec_ref(v___x_1973_);
v_a_1959_ = v___x_1965_;
goto v___jp_1958_;
}
}
}
else
{
lean_dec(v_a_1978_);
lean_dec_ref(v___x_1973_);
v_a_1959_ = v___x_1965_;
goto v___jp_1958_;
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v___x_1973_);
v_a_2059_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_1977_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_1977_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_1969_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_1969_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
v_a_1959_ = v___x_1965_;
goto v___jp_1958_;
}
}
v___jp_1958_:
{
size_t v___x_1960_; size_t v___x_1961_; 
v___x_1960_ = ((size_t)1ULL);
v___x_1961_ = lean_usize_add(v_i_1945_, v___x_1960_);
v_i_1945_ = v___x_1961_;
v_b_1946_ = v_a_1959_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2075_ = _args[0];
lean_object* v_lams_u2081_2076_ = _args[1];
lean_object* v_as_2077_ = _args[2];
lean_object* v_sz_2078_ = _args[3];
lean_object* v_i_2079_ = _args[4];
lean_object* v_b_2080_ = _args[5];
lean_object* v___y_2081_ = _args[6];
lean_object* v___y_2082_ = _args[7];
lean_object* v___y_2083_ = _args[8];
lean_object* v___y_2084_ = _args[9];
lean_object* v___y_2085_ = _args[10];
lean_object* v___y_2086_ = _args[11];
lean_object* v___y_2087_ = _args[12];
lean_object* v___y_2088_ = _args[13];
lean_object* v___y_2089_ = _args[14];
lean_object* v___y_2090_ = _args[15];
lean_object* v___y_2091_ = _args[16];
_start:
{
size_t v_sz_boxed_2092_; size_t v_i_boxed_2093_; lean_object* v_res_2094_; 
v_sz_boxed_2092_ = lean_unbox_usize(v_sz_2078_);
lean_dec(v_sz_2078_);
v_i_boxed_2093_ = lean_unbox_usize(v_i_2079_);
lean_dec(v_i_2079_);
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2075_, v_lams_u2081_2076_, v_as_2077_, v_sz_boxed_2092_, v_i_boxed_2093_, v_b_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v_as_2077_);
lean_dec_ref(v_lams_u2081_2076_);
lean_dec_ref(v_lams_u2082_2075_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2095_, lean_object* v_lams_u2082_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2108_ = lean_array_get_size(v_lams_u2081_2095_);
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = lean_nat_dec_eq(v___x_2108_, v___x_2109_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2111_ = lean_array_get_size(v_lams_u2082_2096_);
v___x_2112_ = lean_nat_dec_eq(v___x_2111_, v___x_2109_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; size_t v_sz_2114_; size_t v___x_2115_; lean_object* v___x_2116_; 
v___x_2113_ = lean_box(0);
v_sz_2114_ = lean_array_size(v_lams_u2081_2095_);
v___x_2115_ = ((size_t)0ULL);
v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2096_, v_lams_u2081_2095_, v_lams_u2081_2095_, v_sz_2114_, v___x_2115_, v___x_2113_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; 
v_unused_2124_ = lean_ctor_get(v___x_2116_, 0);
lean_dec(v_unused_2124_);
v___x_2118_ = v___x_2116_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_dec(v___x_2116_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2113_);
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2113_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
else
{
return v___x_2116_;
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_box(0);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
return v___x_2126_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2129_, lean_object* v_lams_u2082_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2129_, v_lams_u2082_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec_ref(v_lams_u2082_2130_);
lean_dec_ref(v_lams_u2081_2129_);
return v_res_2142_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2143_){
_start:
{
uint8_t v___x_2144_; 
v___x_2144_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2145_){
_start:
{
uint8_t v_res_2146_; lean_object* v_r_2147_; 
v_res_2146_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2145_);
lean_dec_ref(v_x_2145_);
v_r_2147_ = lean_box(v_res_2146_);
return v_r_2147_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2148_, lean_object* v_x_2149_){
_start:
{
uint8_t v___x_2150_; 
v___x_2150_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2151_, lean_object* v_x_2152_){
_start:
{
uint8_t v_res_2153_; lean_object* v_r_2154_; 
v_res_2153_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2151_, v_x_2152_);
lean_dec_ref(v_x_2152_);
v_r_2154_ = lean_box(v_res_2153_);
return v_r_2154_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2155_, lean_object* v_v_2156_, lean_object* v_i_2157_){
_start:
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = lean_array_get_size(v_xs_2155_);
v___x_2159_ = lean_nat_dec_lt(v_i_2157_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; 
lean_dec(v_i_2157_);
v___x_2160_ = lean_box(0);
return v___x_2160_;
}
else
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = lean_array_fget_borrowed(v_xs_2155_, v_i_2157_);
v___x_2162_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2161_, v_v_2156_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = lean_unsigned_to_nat(1u);
v___x_2164_ = lean_nat_add(v_i_2157_, v___x_2163_);
lean_dec(v_i_2157_);
v_i_2157_ = v___x_2164_;
goto _start;
}
else
{
lean_object* v___x_2166_; 
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v_i_2157_);
return v___x_2166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2167_, lean_object* v_v_2168_, lean_object* v_i_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2167_, v_v_2168_, v_i_2169_);
lean_dec_ref(v_v_2168_);
lean_dec_ref(v_xs_2167_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2171_, lean_object* v_v_2172_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_unsigned_to_nat(0u);
v___x_2174_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2171_, v_v_2172_, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2175_, lean_object* v_v_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2175_, v_v_2176_);
lean_dec_ref(v_v_2176_);
lean_dec_ref(v_xs_2175_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2178_, size_t v_x_2179_, lean_object* v_x_2180_){
_start:
{
if (lean_obj_tag(v_x_2178_) == 0)
{
lean_object* v_es_2181_; lean_object* v___x_2182_; size_t v___x_2183_; size_t v___x_2184_; size_t v___x_2185_; lean_object* v_j_2186_; lean_object* v_entry_2187_; 
v_es_2181_ = lean_ctor_get(v_x_2178_, 0);
v___x_2182_ = lean_box(2);
v___x_2183_ = ((size_t)5ULL);
v___x_2184_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2185_ = lean_usize_land(v_x_2179_, v___x_2184_);
v_j_2186_ = lean_usize_to_nat(v___x_2185_);
v_entry_2187_ = lean_array_get(v___x_2182_, v_es_2181_, v_j_2186_);
switch(lean_obj_tag(v_entry_2187_))
{
case 0:
{
lean_object* v_key_2188_; uint8_t v___x_2189_; 
v_key_2188_ = lean_ctor_get(v_entry_2187_, 0);
lean_inc(v_key_2188_);
lean_dec_ref(v_entry_2187_);
v___x_2189_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2180_, v_key_2188_);
lean_dec(v_key_2188_);
if (v___x_2189_ == 0)
{
lean_dec(v_j_2186_);
return v_x_2178_;
}
else
{
lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2197_; 
lean_inc_ref(v_es_2181_);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_x_2178_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_x_2178_, 0);
lean_dec(v_unused_2198_);
v___x_2191_ = v_x_2178_;
v_isShared_2192_ = v_isSharedCheck_2197_;
goto v_resetjp_2190_;
}
else
{
lean_dec(v_x_2178_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2197_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2193_ = lean_array_set(v_es_2181_, v_j_2186_, v___x_2182_);
lean_dec(v_j_2186_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2193_);
v___x_2195_ = v___x_2191_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
case 1:
{
lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2232_; 
lean_inc_ref(v_es_2181_);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_x_2178_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; 
v_unused_2233_ = lean_ctor_get(v_x_2178_, 0);
lean_dec(v_unused_2233_);
v___x_2200_ = v_x_2178_;
v_isShared_2201_ = v_isSharedCheck_2232_;
goto v_resetjp_2199_;
}
else
{
lean_dec(v_x_2178_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2232_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_node_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2231_; 
v_node_2202_ = lean_ctor_get(v_entry_2187_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_entry_2187_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2204_ = v_entry_2187_;
v_isShared_2205_ = v_isSharedCheck_2231_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_node_2202_);
lean_dec(v_entry_2187_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2231_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_entries_2206_; size_t v___x_2207_; lean_object* v_newNode_2208_; lean_object* v___x_2209_; 
v_entries_2206_ = lean_array_set(v_es_2181_, v_j_2186_, v___x_2182_);
v___x_2207_ = lean_usize_shift_right(v_x_2179_, v___x_2183_);
v_newNode_2208_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2202_, v___x_2207_, v_x_2180_);
lean_inc_ref(v_newNode_2208_);
v___x_2209_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2208_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v___x_2211_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v_newNode_2208_);
v___x_2211_ = v___x_2204_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_newNode_2208_);
v___x_2211_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_array_set(v_entries_2206_, v_j_2186_, v___x_2211_);
lean_dec(v_j_2186_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2212_);
v___x_2214_ = v___x_2200_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
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
lean_object* v_val_2217_; lean_object* v_fst_2218_; lean_object* v_snd_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_newNode_2208_);
lean_del_object(v___x_2204_);
v_val_2217_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_val_2217_);
lean_dec_ref(v___x_2209_);
v_fst_2218_ = lean_ctor_get(v_val_2217_, 0);
v_snd_2219_ = lean_ctor_get(v_val_2217_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_val_2217_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2221_ = v_val_2217_;
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_snd_2219_);
lean_inc(v_fst_2218_);
lean_dec(v_val_2217_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2230_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_fst_2218_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_snd_2219_);
v___x_2224_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = lean_array_set(v_entries_2206_, v_j_2186_, v___x_2224_);
lean_dec(v_j_2186_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2225_);
v___x_2227_ = v___x_2200_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2186_);
return v_x_2178_;
}
}
}
else
{
lean_object* v_ks_2234_; lean_object* v_vs_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2249_; 
v_ks_2234_ = lean_ctor_get(v_x_2178_, 0);
v_vs_2235_ = lean_ctor_get(v_x_2178_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_x_2178_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2237_ = v_x_2178_;
v_isShared_2238_ = v_isSharedCheck_2249_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_vs_2235_);
lean_inc(v_ks_2234_);
lean_dec(v_x_2178_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2249_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2234_, v_x_2180_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v___x_2241_; 
if (v_isShared_2238_ == 0)
{
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_ks_2234_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_vs_2235_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
else
{
lean_object* v_val_2243_; lean_object* v_keys_x27_2244_; lean_object* v_vals_x27_2245_; lean_object* v___x_2247_; 
v_val_2243_ = lean_ctor_get(v___x_2239_, 0);
lean_inc_n(v_val_2243_, 2);
lean_dec_ref(v___x_2239_);
v_keys_x27_2244_ = l_Array_eraseIdx___redArg(v_ks_2234_, v_val_2243_);
v_vals_x27_2245_ = l_Array_eraseIdx___redArg(v_vs_2235_, v_val_2243_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 1, v_vals_x27_2245_);
lean_ctor_set(v___x_2237_, 0, v_keys_x27_2244_);
v___x_2247_ = v___x_2237_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_keys_x27_2244_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_vals_x27_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_){
_start:
{
size_t v_x_21947__boxed_2253_; lean_object* v_res_2254_; 
v_x_21947__boxed_2253_ = lean_unbox_usize(v_x_2251_);
lean_dec(v_x_2251_);
v_res_2254_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2250_, v_x_21947__boxed_2253_, v_x_2252_);
lean_dec_ref(v_x_2252_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2255_, lean_object* v_x_2256_){
_start:
{
uint64_t v___x_2257_; size_t v_h_2258_; lean_object* v___x_2259_; 
v___x_2257_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2256_);
v_h_2258_ = lean_uint64_to_usize(v___x_2257_);
v___x_2259_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2255_, v_h_2258_, v_x_2256_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2260_, lean_object* v_x_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2260_, v_x_2261_);
lean_dec_ref(v_x_2261_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
if (lean_obj_tag(v_as_2263_) == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_box(0);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
return v___x_2276_;
}
else
{
lean_object* v_head_2277_; lean_object* v_tail_2278_; lean_object* v___x_2279_; 
v_head_2277_ = lean_ctor_get(v_as_2263_, 0);
lean_inc(v_head_2277_);
v_tail_2278_ = lean_ctor_get(v_as_2263_, 1);
lean_inc(v_tail_2278_);
lean_dec_ref(v_as_2263_);
v___x_2279_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2277_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_dec_ref(v___x_2279_);
v_as_2263_ = v_tail_2278_;
goto _start;
}
else
{
lean_dec(v_tail_2278_);
return v___x_2279_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec(v___y_2282_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2294_, lean_object* v_vals_2295_, lean_object* v_i_2296_, lean_object* v_k_2297_){
_start:
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = lean_array_get_size(v_keys_2294_);
v___x_2299_ = lean_nat_dec_lt(v_i_2296_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; 
lean_dec(v_i_2296_);
v___x_2300_ = lean_box(0);
return v___x_2300_;
}
else
{
lean_object* v_k_x27_2301_; uint8_t v___x_2302_; 
v_k_x27_2301_ = lean_array_fget_borrowed(v_keys_2294_, v_i_2296_);
v___x_2302_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_2297_, v_k_x27_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_unsigned_to_nat(1u);
v___x_2304_ = lean_nat_add(v_i_2296_, v___x_2303_);
lean_dec(v_i_2296_);
v_i_2296_ = v___x_2304_;
goto _start;
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_array_fget_borrowed(v_vals_2295_, v_i_2296_);
lean_dec(v_i_2296_);
lean_inc(v___x_2306_);
v___x_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2308_, lean_object* v_vals_2309_, lean_object* v_i_2310_, lean_object* v_k_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2308_, v_vals_2309_, v_i_2310_, v_k_2311_);
lean_dec_ref(v_k_2311_);
lean_dec_ref(v_vals_2309_);
lean_dec_ref(v_keys_2308_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2313_, size_t v_x_2314_, lean_object* v_x_2315_){
_start:
{
if (lean_obj_tag(v_x_2313_) == 0)
{
lean_object* v_es_2316_; lean_object* v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; lean_object* v_j_2321_; lean_object* v___x_2322_; 
v_es_2316_ = lean_ctor_get(v_x_2313_, 0);
v___x_2317_ = lean_box(2);
v___x_2318_ = ((size_t)5ULL);
v___x_2319_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2320_ = lean_usize_land(v_x_2314_, v___x_2319_);
v_j_2321_ = lean_usize_to_nat(v___x_2320_);
v___x_2322_ = lean_array_get_borrowed(v___x_2317_, v_es_2316_, v_j_2321_);
lean_dec(v_j_2321_);
switch(lean_obj_tag(v___x_2322_))
{
case 0:
{
lean_object* v_key_2323_; lean_object* v_val_2324_; uint8_t v___x_2325_; 
v_key_2323_ = lean_ctor_get(v___x_2322_, 0);
v_val_2324_ = lean_ctor_get(v___x_2322_, 1);
v___x_2325_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2315_, v_key_2323_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_box(0);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; 
lean_inc(v_val_2324_);
v___x_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_val_2324_);
return v___x_2327_;
}
}
case 1:
{
lean_object* v_node_2328_; size_t v___x_2329_; 
v_node_2328_ = lean_ctor_get(v___x_2322_, 0);
v___x_2329_ = lean_usize_shift_right(v_x_2314_, v___x_2318_);
v_x_2313_ = v_node_2328_;
v_x_2314_ = v___x_2329_;
goto _start;
}
default: 
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_box(0);
return v___x_2331_;
}
}
}
else
{
lean_object* v_ks_2332_; lean_object* v_vs_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_ks_2332_ = lean_ctor_get(v_x_2313_, 0);
v_vs_2333_ = lean_ctor_get(v_x_2313_, 1);
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2332_, v_vs_2333_, v___x_2334_, v_x_2315_);
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_){
_start:
{
size_t v_x_22166__boxed_2339_; lean_object* v_res_2340_; 
v_x_22166__boxed_2339_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_res_2340_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2336_, v_x_22166__boxed_2339_, v_x_2338_);
lean_dec_ref(v_x_2338_);
lean_dec_ref(v_x_2336_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
uint64_t v___x_2343_; size_t v___x_2344_; lean_object* v___x_2345_; 
v___x_2343_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2342_);
v___x_2344_ = lean_uint64_to_usize(v___x_2343_);
v___x_2345_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2341_, v___x_2344_, v_x_2342_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2346_, v_x_2347_);
lean_dec_ref(v_x_2347_);
lean_dec_ref(v_x_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2349_, lean_object* v_b_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
if (lean_obj_tag(v_as_x27_2349_) == 0)
{
lean_object* v___x_2362_; 
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v_b_2350_);
return v___x_2362_;
}
else
{
lean_object* v_head_2363_; lean_object* v_tail_2364_; lean_object* v___x_2365_; lean_object* v_toGoalState_2366_; lean_object* v_ematch_2367_; lean_object* v_delayedThmInsts_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_head_2363_ = lean_ctor_get(v_as_x27_2349_, 0);
v_tail_2364_ = lean_ctor_get(v_as_x27_2349_, 1);
v___x_2365_ = lean_st_ref_get(v___y_2351_);
v_toGoalState_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc_ref(v_toGoalState_2366_);
lean_dec(v___x_2365_);
v_ematch_2367_ = lean_ctor_get(v_toGoalState_2366_, 12);
lean_inc_ref(v_ematch_2367_);
lean_dec_ref(v_toGoalState_2366_);
v_delayedThmInsts_2368_ = lean_ctor_get(v_ematch_2367_, 10);
lean_inc_ref(v_delayedThmInsts_2368_);
lean_dec_ref(v_ematch_2367_);
v___x_2369_ = lean_box(0);
v___x_2370_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2368_, v_head_2363_);
lean_dec_ref(v_delayedThmInsts_2368_);
if (lean_obj_tag(v___x_2370_) == 1)
{
lean_object* v_val_2371_; lean_object* v___x_2372_; lean_object* v_toGoalState_2373_; lean_object* v_ematch_2374_; lean_object* v_mvarId_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2429_; 
v_val_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_val_2371_);
lean_dec_ref(v___x_2370_);
v___x_2372_ = lean_st_ref_take(v___y_2351_);
v_toGoalState_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc_ref(v_toGoalState_2373_);
v_ematch_2374_ = lean_ctor_get(v_toGoalState_2373_, 12);
lean_inc_ref(v_ematch_2374_);
v_mvarId_2375_ = lean_ctor_get(v___x_2372_, 1);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v___x_2372_, 0);
lean_dec(v_unused_2430_);
v___x_2377_ = v___x_2372_;
v_isShared_2378_ = v_isSharedCheck_2429_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_mvarId_2375_);
lean_dec(v___x_2372_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2429_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v_nextDeclIdx_2379_; lean_object* v_enodeMap_2380_; lean_object* v_exprs_2381_; lean_object* v_parents_2382_; lean_object* v_congrTable_2383_; lean_object* v_appMap_2384_; lean_object* v_indicesFound_2385_; lean_object* v_newFacts_2386_; uint8_t v_inconsistent_2387_; lean_object* v_nextIdx_2388_; lean_object* v_newRawFacts_2389_; lean_object* v_facts_2390_; lean_object* v_extThms_2391_; lean_object* v_inj_2392_; lean_object* v_split_2393_; lean_object* v_clean_2394_; lean_object* v_sstates_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2427_; 
v_nextDeclIdx_2379_ = lean_ctor_get(v_toGoalState_2373_, 0);
v_enodeMap_2380_ = lean_ctor_get(v_toGoalState_2373_, 1);
v_exprs_2381_ = lean_ctor_get(v_toGoalState_2373_, 2);
v_parents_2382_ = lean_ctor_get(v_toGoalState_2373_, 3);
v_congrTable_2383_ = lean_ctor_get(v_toGoalState_2373_, 4);
v_appMap_2384_ = lean_ctor_get(v_toGoalState_2373_, 5);
v_indicesFound_2385_ = lean_ctor_get(v_toGoalState_2373_, 6);
v_newFacts_2386_ = lean_ctor_get(v_toGoalState_2373_, 7);
v_inconsistent_2387_ = lean_ctor_get_uint8(v_toGoalState_2373_, sizeof(void*)*17);
v_nextIdx_2388_ = lean_ctor_get(v_toGoalState_2373_, 8);
v_newRawFacts_2389_ = lean_ctor_get(v_toGoalState_2373_, 9);
v_facts_2390_ = lean_ctor_get(v_toGoalState_2373_, 10);
v_extThms_2391_ = lean_ctor_get(v_toGoalState_2373_, 11);
v_inj_2392_ = lean_ctor_get(v_toGoalState_2373_, 13);
v_split_2393_ = lean_ctor_get(v_toGoalState_2373_, 14);
v_clean_2394_ = lean_ctor_get(v_toGoalState_2373_, 15);
v_sstates_2395_ = lean_ctor_get(v_toGoalState_2373_, 16);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_toGoalState_2373_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; 
v_unused_2428_ = lean_ctor_get(v_toGoalState_2373_, 12);
lean_dec(v_unused_2428_);
v___x_2397_ = v_toGoalState_2373_;
v_isShared_2398_ = v_isSharedCheck_2427_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_sstates_2395_);
lean_inc(v_clean_2394_);
lean_inc(v_split_2393_);
lean_inc(v_inj_2392_);
lean_inc(v_extThms_2391_);
lean_inc(v_facts_2390_);
lean_inc(v_newRawFacts_2389_);
lean_inc(v_nextIdx_2388_);
lean_inc(v_newFacts_2386_);
lean_inc(v_indicesFound_2385_);
lean_inc(v_appMap_2384_);
lean_inc(v_congrTable_2383_);
lean_inc(v_parents_2382_);
lean_inc(v_exprs_2381_);
lean_inc(v_enodeMap_2380_);
lean_inc(v_nextDeclIdx_2379_);
lean_dec(v_toGoalState_2373_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2427_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_thmMap_2399_; lean_object* v_gmt_2400_; lean_object* v_thms_2401_; lean_object* v_newThms_2402_; lean_object* v_numInstances_2403_; lean_object* v_numDelayedInstances_2404_; lean_object* v_num_2405_; lean_object* v_preInstances_2406_; lean_object* v_nextThmIdx_2407_; lean_object* v_matchEqNames_2408_; lean_object* v_delayedThmInsts_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2426_; 
v_thmMap_2399_ = lean_ctor_get(v_ematch_2374_, 0);
v_gmt_2400_ = lean_ctor_get(v_ematch_2374_, 1);
v_thms_2401_ = lean_ctor_get(v_ematch_2374_, 2);
v_newThms_2402_ = lean_ctor_get(v_ematch_2374_, 3);
v_numInstances_2403_ = lean_ctor_get(v_ematch_2374_, 4);
v_numDelayedInstances_2404_ = lean_ctor_get(v_ematch_2374_, 5);
v_num_2405_ = lean_ctor_get(v_ematch_2374_, 6);
v_preInstances_2406_ = lean_ctor_get(v_ematch_2374_, 7);
v_nextThmIdx_2407_ = lean_ctor_get(v_ematch_2374_, 8);
v_matchEqNames_2408_ = lean_ctor_get(v_ematch_2374_, 9);
v_delayedThmInsts_2409_ = lean_ctor_get(v_ematch_2374_, 10);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_ematch_2374_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2411_ = v_ematch_2374_;
v_isShared_2412_ = v_isSharedCheck_2426_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_delayedThmInsts_2409_);
lean_inc(v_matchEqNames_2408_);
lean_inc(v_nextThmIdx_2407_);
lean_inc(v_preInstances_2406_);
lean_inc(v_num_2405_);
lean_inc(v_numDelayedInstances_2404_);
lean_inc(v_numInstances_2403_);
lean_inc(v_newThms_2402_);
lean_inc(v_thms_2401_);
lean_inc(v_gmt_2400_);
lean_inc(v_thmMap_2399_);
lean_dec(v_ematch_2374_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2426_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2409_, v_head_2363_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 10, v___x_2413_);
v___x_2415_ = v___x_2411_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_thmMap_2399_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_gmt_2400_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_thms_2401_);
lean_ctor_set(v_reuseFailAlloc_2425_, 3, v_newThms_2402_);
lean_ctor_set(v_reuseFailAlloc_2425_, 4, v_numInstances_2403_);
lean_ctor_set(v_reuseFailAlloc_2425_, 5, v_numDelayedInstances_2404_);
lean_ctor_set(v_reuseFailAlloc_2425_, 6, v_num_2405_);
lean_ctor_set(v_reuseFailAlloc_2425_, 7, v_preInstances_2406_);
lean_ctor_set(v_reuseFailAlloc_2425_, 8, v_nextThmIdx_2407_);
lean_ctor_set(v_reuseFailAlloc_2425_, 9, v_matchEqNames_2408_);
lean_ctor_set(v_reuseFailAlloc_2425_, 10, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2417_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 12, v___x_2415_);
v___x_2417_ = v___x_2397_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_nextDeclIdx_2379_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_enodeMap_2380_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_exprs_2381_);
lean_ctor_set(v_reuseFailAlloc_2424_, 3, v_parents_2382_);
lean_ctor_set(v_reuseFailAlloc_2424_, 4, v_congrTable_2383_);
lean_ctor_set(v_reuseFailAlloc_2424_, 5, v_appMap_2384_);
lean_ctor_set(v_reuseFailAlloc_2424_, 6, v_indicesFound_2385_);
lean_ctor_set(v_reuseFailAlloc_2424_, 7, v_newFacts_2386_);
lean_ctor_set(v_reuseFailAlloc_2424_, 8, v_nextIdx_2388_);
lean_ctor_set(v_reuseFailAlloc_2424_, 9, v_newRawFacts_2389_);
lean_ctor_set(v_reuseFailAlloc_2424_, 10, v_facts_2390_);
lean_ctor_set(v_reuseFailAlloc_2424_, 11, v_extThms_2391_);
lean_ctor_set(v_reuseFailAlloc_2424_, 12, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2424_, 13, v_inj_2392_);
lean_ctor_set(v_reuseFailAlloc_2424_, 14, v_split_2393_);
lean_ctor_set(v_reuseFailAlloc_2424_, 15, v_clean_2394_);
lean_ctor_set(v_reuseFailAlloc_2424_, 16, v_sstates_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, sizeof(void*)*17, v_inconsistent_2387_);
v___x_2417_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2419_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2417_);
v___x_2419_ = v___x_2377_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_mvarId_2375_);
v___x_2419_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_st_ref_set(v___y_2351_, v___x_2419_);
v___x_2421_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2371_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_dec_ref(v___x_2421_);
v_as_x27_2349_ = v_tail_2364_;
v_b_2350_ = v___x_2369_;
goto _start;
}
else
{
return v___x_2421_;
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
lean_dec(v___x_2370_);
v_as_x27_2349_ = v_tail_2364_;
v_b_2350_ = v___x_2369_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2432_, lean_object* v_b_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2432_, v_b_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec(v_as_x27_2432_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2447_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2487_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2487_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2487_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
uint8_t v___x_2463_; 
v___x_2463_ = lean_unbox(v_a_2459_);
lean_dec(v_a_2459_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v_toGoalState_2465_; lean_object* v_ematch_2466_; lean_object* v_delayedThmInsts_2467_; uint8_t v___x_2468_; 
v___x_2464_ = lean_st_ref_get(v_a_2447_);
v_toGoalState_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc_ref(v_toGoalState_2465_);
lean_dec(v___x_2464_);
v_ematch_2466_ = lean_ctor_get(v_toGoalState_2465_, 12);
lean_inc_ref(v_ematch_2466_);
lean_dec_ref(v_toGoalState_2465_);
v_delayedThmInsts_2467_ = lean_ctor_get(v_ematch_2466_, 10);
lean_inc_ref(v_delayedThmInsts_2467_);
lean_dec_ref(v_ematch_2466_);
v___x_2468_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2467_);
lean_dec_ref(v_delayedThmInsts_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_del_object(v___x_2461_);
v___x_2469_ = lean_box(0);
v___x_2470_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2446_, v___x_2469_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v___x_2470_, 0);
lean_dec(v_unused_2478_);
v___x_2472_ = v___x_2470_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_dec(v___x_2470_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2469_);
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2469_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
else
{
return v___x_2470_;
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = lean_box(0);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2479_);
v___x_2481_ = v___x_2461_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2483_ = lean_box(0);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2483_);
v___x_2485_ = v___x_2461_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
v_a_2488_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2458_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2458_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec(v_toPropagateDown_2496_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2510_, v_x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2513_, v_x_2514_, v_x_2515_);
lean_dec_ref(v_x_2515_);
lean_dec_ref(v_x_2514_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2517_, lean_object* v_x_2518_, lean_object* v_x_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2518_, v_x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2521_, v_x_2522_, v_x_2523_);
lean_dec_ref(v_x_2523_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2525_, lean_object* v_as_x27_2526_, lean_object* v_b_2527_, lean_object* v_a_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2526_, v_b_2527_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2541_, lean_object* v_as_x27_2542_, lean_object* v_b_2543_, lean_object* v_a_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2541_, v_as_x27_2542_, v_b_2543_, v_a_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec(v_as_x27_2542_);
lean_dec(v_as_2541_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2557_, lean_object* v_x_2558_, size_t v_x_2559_, lean_object* v_x_2560_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2558_, v_x_2559_, v_x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_, lean_object* v_x_2565_){
_start:
{
size_t v_x_22463__boxed_2566_; lean_object* v_res_2567_; 
v_x_22463__boxed_2566_ = lean_unbox_usize(v_x_2564_);
lean_dec(v_x_2564_);
v_res_2567_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2562_, v_x_2563_, v_x_22463__boxed_2566_, v_x_2565_);
lean_dec_ref(v_x_2565_);
lean_dec_ref(v_x_2563_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2568_, lean_object* v_x_2569_, size_t v_x_2570_, lean_object* v_x_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2569_, v_x_2570_, v_x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2573_, lean_object* v_x_2574_, lean_object* v_x_2575_, lean_object* v_x_2576_){
_start:
{
size_t v_x_22474__boxed_2577_; lean_object* v_res_2578_; 
v_x_22474__boxed_2577_ = lean_unbox_usize(v_x_2575_);
lean_dec(v_x_2575_);
v_res_2578_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2573_, v_x_2574_, v_x_22474__boxed_2577_, v_x_2576_);
lean_dec_ref(v_x_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2579_, lean_object* v_keys_2580_, lean_object* v_vals_2581_, lean_object* v_heq_2582_, lean_object* v_i_2583_, lean_object* v_k_2584_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2580_, v_vals_2581_, v_i_2583_, v_k_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2586_, lean_object* v_keys_2587_, lean_object* v_vals_2588_, lean_object* v_heq_2589_, lean_object* v_i_2590_, lean_object* v_k_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2586_, v_keys_2587_, v_vals_2588_, v_heq_2589_, v_i_2590_, v_k_2591_);
lean_dec_ref(v_k_2591_);
lean_dec_ref(v_vals_2588_);
lean_dec_ref(v_keys_2587_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2593_, lean_object* v_keys_2594_, lean_object* v_vals_2595_, lean_object* v_i_2596_, lean_object* v_k_2597_){
_start:
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = lean_array_get_size(v_keys_2594_);
v___x_2599_ = lean_nat_dec_lt(v_i_2596_, v___x_2598_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; 
lean_dec_ref(v_k_2597_);
lean_dec(v_i_2596_);
v___x_2600_ = lean_box(0);
return v___x_2600_;
}
else
{
lean_object* v_k_x27_2601_; uint8_t v___x_2602_; 
v_k_x27_2601_ = lean_array_fget_borrowed(v_keys_2594_, v_i_2596_);
lean_inc(v_k_x27_2601_);
lean_inc_ref(v_k_2597_);
v___x_2602_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2593_, v_k_2597_, v_k_x27_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = lean_unsigned_to_nat(1u);
v___x_2604_ = lean_nat_add(v_i_2596_, v___x_2603_);
lean_dec(v_i_2596_);
v_i_2596_ = v___x_2604_;
goto _start;
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec_ref(v_k_2597_);
v___x_2606_ = lean_array_fget_borrowed(v_vals_2595_, v_i_2596_);
lean_dec(v_i_2596_);
lean_inc(v___x_2606_);
lean_inc(v_k_x27_2601_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v_k_x27_2601_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
return v___x_2608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2609_, lean_object* v_keys_2610_, lean_object* v_vals_2611_, lean_object* v_i_2612_, lean_object* v_k_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2609_, v_keys_2610_, v_vals_2611_, v_i_2612_, v_k_2613_);
lean_dec_ref(v_vals_2611_);
lean_dec_ref(v_keys_2610_);
lean_dec_ref(v___x_2609_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2615_, lean_object* v_x_2616_, size_t v_x_2617_, lean_object* v_x_2618_){
_start:
{
if (lean_obj_tag(v_x_2616_) == 0)
{
lean_object* v_es_2619_; lean_object* v___x_2620_; size_t v___x_2621_; size_t v___x_2622_; size_t v___x_2623_; lean_object* v_j_2624_; lean_object* v___x_2625_; 
v_es_2619_ = lean_ctor_get(v_x_2616_, 0);
lean_inc_ref(v_es_2619_);
lean_dec_ref(v_x_2616_);
v___x_2620_ = lean_box(2);
v___x_2621_ = ((size_t)5ULL);
v___x_2622_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2623_ = lean_usize_land(v_x_2617_, v___x_2622_);
v_j_2624_ = lean_usize_to_nat(v___x_2623_);
v___x_2625_ = lean_array_get(v___x_2620_, v_es_2619_, v_j_2624_);
lean_dec(v_j_2624_);
lean_dec_ref(v_es_2619_);
switch(lean_obj_tag(v___x_2625_))
{
case 0:
{
lean_object* v_key_2626_; lean_object* v_val_2627_; uint8_t v___x_2628_; 
v_key_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc_n(v_key_2626_, 2);
v_val_2627_ = lean_ctor_get(v___x_2625_, 1);
lean_inc(v_val_2627_);
lean_dec_ref(v___x_2625_);
v___x_2628_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2615_, v_x_2618_, v_key_2626_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; 
lean_dec(v_val_2627_);
lean_dec(v_key_2626_);
v___x_2629_ = lean_box(0);
return v___x_2629_;
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v_key_2626_);
lean_ctor_set(v___x_2630_, 1, v_val_2627_);
v___x_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
return v___x_2631_;
}
}
case 1:
{
lean_object* v_node_2632_; size_t v___x_2633_; 
v_node_2632_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_node_2632_);
lean_dec_ref(v___x_2625_);
v___x_2633_ = lean_usize_shift_right(v_x_2617_, v___x_2621_);
v_x_2616_ = v_node_2632_;
v_x_2617_ = v___x_2633_;
goto _start;
}
default: 
{
lean_object* v___x_2635_; 
lean_dec_ref(v_x_2618_);
v___x_2635_ = lean_box(0);
return v___x_2635_;
}
}
}
else
{
lean_object* v_ks_2636_; lean_object* v_vs_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_ks_2636_ = lean_ctor_get(v_x_2616_, 0);
lean_inc_ref(v_ks_2636_);
v_vs_2637_ = lean_ctor_get(v_x_2616_, 1);
lean_inc_ref(v_vs_2637_);
lean_dec_ref(v_x_2616_);
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2615_, v_ks_2636_, v_vs_2637_, v___x_2638_, v_x_2618_);
lean_dec_ref(v_vs_2637_);
lean_dec_ref(v_ks_2636_);
return v___x_2639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_, lean_object* v_x_2643_){
_start:
{
size_t v_x_27417__boxed_2644_; lean_object* v_res_2645_; 
v_x_27417__boxed_2644_ = lean_unbox_usize(v_x_2642_);
lean_dec(v_x_2642_);
v_res_2645_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2640_, v_x_2641_, v_x_27417__boxed_2644_, v_x_2643_);
lean_dec_ref(v___x_2640_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2646_, lean_object* v_x_2647_, lean_object* v_x_2648_){
_start:
{
uint64_t v___x_2649_; size_t v___x_2650_; lean_object* v___x_2651_; 
lean_inc_ref(v_x_2648_);
v___x_2649_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2646_, v_x_2648_);
v___x_2650_ = lean_uint64_to_usize(v___x_2649_);
lean_inc_ref(v_x_2647_);
v___x_2651_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2646_, v_x_2647_, v___x_2650_, v_x_2648_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2652_, lean_object* v_x_2653_, lean_object* v_x_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2652_, v_x_2653_, v_x_2654_);
lean_dec_ref(v_x_2653_);
lean_dec_ref(v___x_2652_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2656_, lean_object* v_x_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_, lean_object* v_x_2660_){
_start:
{
lean_object* v_ks_2661_; lean_object* v_vs_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2686_; 
v_ks_2661_ = lean_ctor_get(v_x_2657_, 0);
v_vs_2662_ = lean_ctor_get(v_x_2657_, 1);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_x_2657_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2664_ = v_x_2657_;
v_isShared_2665_ = v_isSharedCheck_2686_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_vs_2662_);
lean_inc(v_ks_2661_);
lean_dec(v_x_2657_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2686_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2666_ = lean_array_get_size(v_ks_2661_);
v___x_2667_ = lean_nat_dec_lt(v_x_2658_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
lean_dec(v_x_2658_);
v___x_2668_ = lean_array_push(v_ks_2661_, v_x_2659_);
v___x_2669_ = lean_array_push(v_vs_2662_, v_x_2660_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 1, v___x_2669_);
lean_ctor_set(v___x_2664_, 0, v___x_2668_);
v___x_2671_ = v___x_2664_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
else
{
lean_object* v_k_x27_2673_; uint8_t v___x_2674_; 
v_k_x27_2673_ = lean_array_fget_borrowed(v_ks_2661_, v_x_2658_);
lean_inc(v_k_x27_2673_);
lean_inc_ref(v_x_2659_);
v___x_2674_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2656_, v_x_2659_, v_k_x27_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2676_; 
if (v_isShared_2665_ == 0)
{
v___x_2676_ = v___x_2664_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_ks_2661_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_vs_2662_);
v___x_2676_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_unsigned_to_nat(1u);
v___x_2678_ = lean_nat_add(v_x_2658_, v___x_2677_);
lean_dec(v_x_2658_);
v_x_2657_ = v___x_2676_;
v_x_2658_ = v___x_2678_;
goto _start;
}
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2681_ = lean_array_fset(v_ks_2661_, v_x_2658_, v_x_2659_);
v___x_2682_ = lean_array_fset(v_vs_2662_, v_x_2658_, v_x_2660_);
lean_dec(v_x_2658_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 1, v___x_2682_);
lean_ctor_set(v___x_2664_, 0, v___x_2681_);
v___x_2684_ = v___x_2664_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_, lean_object* v_x_2690_, lean_object* v_x_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2687_, v_x_2688_, v_x_2689_, v_x_2690_, v_x_2691_);
lean_dec_ref(v___x_2687_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2693_, lean_object* v_n_2694_, lean_object* v_k_2695_, lean_object* v_v_2696_){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2693_, v_n_2694_, v___x_2697_, v_k_2695_, v_v_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2699_, lean_object* v_n_2700_, lean_object* v_k_2701_, lean_object* v_v_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2699_, v_n_2700_, v_k_2701_, v_v_2702_);
lean_dec_ref(v___x_2699_);
return v_res_2703_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2705_, lean_object* v_x_2706_, size_t v_x_2707_, size_t v_x_2708_, lean_object* v_x_2709_, lean_object* v_x_2710_){
_start:
{
if (lean_obj_tag(v_x_2706_) == 0)
{
lean_object* v_es_2711_; size_t v___x_2712_; size_t v___x_2713_; size_t v___x_2714_; size_t v___x_2715_; lean_object* v_j_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v_es_2711_ = lean_ctor_get(v_x_2706_, 0);
v___x_2712_ = ((size_t)5ULL);
v___x_2713_ = ((size_t)1ULL);
v___x_2714_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2715_ = lean_usize_land(v_x_2707_, v___x_2714_);
v_j_2716_ = lean_usize_to_nat(v___x_2715_);
v___x_2717_ = lean_array_get_size(v_es_2711_);
v___x_2718_ = lean_nat_dec_lt(v_j_2716_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_dec(v_j_2716_);
lean_dec(v_x_2710_);
lean_dec_ref(v_x_2709_);
return v_x_2706_;
}
else
{
lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2755_; 
lean_inc_ref(v_es_2711_);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_x_2706_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v_x_2706_, 0);
lean_dec(v_unused_2756_);
v___x_2720_ = v_x_2706_;
v_isShared_2721_ = v_isSharedCheck_2755_;
goto v_resetjp_2719_;
}
else
{
lean_dec(v_x_2706_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2755_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v_v_2722_; lean_object* v___x_2723_; lean_object* v_xs_x27_2724_; lean_object* v___y_2726_; 
v_v_2722_ = lean_array_fget(v_es_2711_, v_j_2716_);
v___x_2723_ = lean_box(0);
v_xs_x27_2724_ = lean_array_fset(v_es_2711_, v_j_2716_, v___x_2723_);
switch(lean_obj_tag(v_v_2722_))
{
case 0:
{
lean_object* v_key_2731_; lean_object* v_val_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2742_; 
v_key_2731_ = lean_ctor_get(v_v_2722_, 0);
v_val_2732_ = lean_ctor_get(v_v_2722_, 1);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_v_2722_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2734_ = v_v_2722_;
v_isShared_2735_ = v_isSharedCheck_2742_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_val_2732_);
lean_inc(v_key_2731_);
lean_dec(v_v_2722_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2742_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
uint8_t v___x_2736_; 
lean_inc(v_key_2731_);
lean_inc_ref(v_x_2709_);
v___x_2736_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2705_, v_x_2709_, v_key_2731_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_del_object(v___x_2734_);
v___x_2737_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2731_, v_val_2732_, v_x_2709_, v_x_2710_);
v___x_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
v___y_2726_ = v___x_2738_;
goto v___jp_2725_;
}
else
{
lean_object* v___x_2740_; 
lean_dec(v_val_2732_);
lean_dec(v_key_2731_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v_x_2710_);
lean_ctor_set(v___x_2734_, 0, v_x_2709_);
v___x_2740_ = v___x_2734_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_x_2709_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_x_2710_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
v___y_2726_ = v___x_2740_;
goto v___jp_2725_;
}
}
}
}
case 1:
{
lean_object* v_node_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2753_; 
v_node_2743_ = lean_ctor_get(v_v_2722_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_v_2722_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2745_ = v_v_2722_;
v_isShared_2746_ = v_isSharedCheck_2753_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_node_2743_);
lean_dec(v_v_2722_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2753_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
size_t v___x_2747_; size_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2747_ = lean_usize_shift_right(v_x_2707_, v___x_2712_);
v___x_2748_ = lean_usize_add(v_x_2708_, v___x_2713_);
v___x_2749_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2705_, v_node_2743_, v___x_2747_, v___x_2748_, v_x_2709_, v_x_2710_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2749_);
v___x_2751_ = v___x_2745_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
v___y_2726_ = v___x_2751_;
goto v___jp_2725_;
}
}
}
default: 
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_x_2709_);
lean_ctor_set(v___x_2754_, 1, v_x_2710_);
v___y_2726_ = v___x_2754_;
goto v___jp_2725_;
}
}
v___jp_2725_:
{
lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2727_ = lean_array_fset(v_xs_x27_2724_, v_j_2716_, v___y_2726_);
lean_dec(v_j_2716_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2727_);
v___x_2729_ = v___x_2720_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
else
{
lean_object* v_ks_2757_; lean_object* v_vs_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2778_; 
v_ks_2757_ = lean_ctor_get(v_x_2706_, 0);
v_vs_2758_ = lean_ctor_get(v_x_2706_, 1);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_x_2706_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2760_ = v_x_2706_;
v_isShared_2761_ = v_isSharedCheck_2778_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_vs_2758_);
lean_inc(v_ks_2757_);
lean_dec(v_x_2706_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2778_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_ks_2757_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_vs_2758_);
v___x_2763_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v_newNode_2764_; uint8_t v___y_2766_; size_t v___x_2772_; uint8_t v___x_2773_; 
v_newNode_2764_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2705_, v___x_2763_, v_x_2709_, v_x_2710_);
v___x_2772_ = ((size_t)7ULL);
v___x_2773_ = lean_usize_dec_le(v___x_2772_, v_x_2708_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v___x_2774_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2764_);
v___x_2775_ = lean_unsigned_to_nat(4u);
v___x_2776_ = lean_nat_dec_lt(v___x_2774_, v___x_2775_);
lean_dec(v___x_2774_);
v___y_2766_ = v___x_2776_;
goto v___jp_2765_;
}
else
{
v___y_2766_ = v___x_2773_;
goto v___jp_2765_;
}
v___jp_2765_:
{
if (v___y_2766_ == 0)
{
lean_object* v_ks_2767_; lean_object* v_vs_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_ks_2767_ = lean_ctor_get(v_newNode_2764_, 0);
lean_inc_ref(v_ks_2767_);
v_vs_2768_ = lean_ctor_get(v_newNode_2764_, 1);
lean_inc_ref(v_vs_2768_);
lean_dec_ref(v_newNode_2764_);
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2771_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2705_, v_x_2708_, v_ks_2767_, v_vs_2768_, v___x_2769_, v___x_2770_);
lean_dec_ref(v_vs_2768_);
lean_dec_ref(v_ks_2767_);
return v___x_2771_;
}
else
{
return v_newNode_2764_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2779_, size_t v_depth_2780_, lean_object* v_keys_2781_, lean_object* v_vals_2782_, lean_object* v_i_2783_, lean_object* v_entries_2784_){
_start:
{
lean_object* v___x_2785_; uint8_t v___x_2786_; 
v___x_2785_ = lean_array_get_size(v_keys_2781_);
v___x_2786_ = lean_nat_dec_lt(v_i_2783_, v___x_2785_);
if (v___x_2786_ == 0)
{
lean_dec(v_i_2783_);
return v_entries_2784_;
}
else
{
lean_object* v_k_2787_; lean_object* v_v_2788_; uint64_t v___x_2789_; size_t v_h_2790_; size_t v___x_2791_; lean_object* v___x_2792_; size_t v___x_2793_; size_t v___x_2794_; size_t v___x_2795_; size_t v_h_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_k_2787_ = lean_array_fget_borrowed(v_keys_2781_, v_i_2783_);
v_v_2788_ = lean_array_fget_borrowed(v_vals_2782_, v_i_2783_);
lean_inc_n(v_k_2787_, 2);
v___x_2789_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2779_, v_k_2787_);
v_h_2790_ = lean_uint64_to_usize(v___x_2789_);
v___x_2791_ = ((size_t)5ULL);
v___x_2792_ = lean_unsigned_to_nat(1u);
v___x_2793_ = ((size_t)1ULL);
v___x_2794_ = lean_usize_sub(v_depth_2780_, v___x_2793_);
v___x_2795_ = lean_usize_mul(v___x_2791_, v___x_2794_);
v_h_2796_ = lean_usize_shift_right(v_h_2790_, v___x_2795_);
v___x_2797_ = lean_nat_add(v_i_2783_, v___x_2792_);
lean_dec(v_i_2783_);
lean_inc(v_v_2788_);
v___x_2798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2779_, v_entries_2784_, v_h_2796_, v_depth_2780_, v_k_2787_, v_v_2788_);
v_i_2783_ = v___x_2797_;
v_entries_2784_ = v___x_2798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2800_, lean_object* v_depth_2801_, lean_object* v_keys_2802_, lean_object* v_vals_2803_, lean_object* v_i_2804_, lean_object* v_entries_2805_){
_start:
{
size_t v_depth_boxed_2806_; lean_object* v_res_2807_; 
v_depth_boxed_2806_ = lean_unbox_usize(v_depth_2801_);
lean_dec(v_depth_2801_);
v_res_2807_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2800_, v_depth_boxed_2806_, v_keys_2802_, v_vals_2803_, v_i_2804_, v_entries_2805_);
lean_dec_ref(v_vals_2803_);
lean_dec_ref(v_keys_2802_);
lean_dec_ref(v___x_2800_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_, lean_object* v_x_2813_){
_start:
{
size_t v_x_27579__boxed_2814_; size_t v_x_27580__boxed_2815_; lean_object* v_res_2816_; 
v_x_27579__boxed_2814_ = lean_unbox_usize(v_x_2810_);
lean_dec(v_x_2810_);
v_x_27580__boxed_2815_ = lean_unbox_usize(v_x_2811_);
lean_dec(v_x_2811_);
v_res_2816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2808_, v_x_2809_, v_x_27579__boxed_2814_, v_x_27580__boxed_2815_, v_x_2812_, v_x_2813_);
lean_dec_ref(v___x_2808_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_, lean_object* v_x_2820_){
_start:
{
uint64_t v___x_2821_; size_t v___x_2822_; size_t v___x_2823_; lean_object* v___x_2824_; 
lean_inc_ref(v_x_2819_);
v___x_2821_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2817_, v_x_2819_);
v___x_2822_ = lean_uint64_to_usize(v___x_2821_);
v___x_2823_ = ((size_t)1ULL);
v___x_2824_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2817_, v_x_2818_, v___x_2822_, v___x_2823_, v_x_2819_, v_x_2820_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_, lean_object* v_x_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2825_, v_x_2826_, v_x_2827_, v_x_2828_);
lean_dec_ref(v___x_2825_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2834_, lean_object* v_rootNew_2835_, uint8_t v_a_2836_, lean_object* v_b_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v___x_2845_; lean_object* v_snd_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_3011_; 
v___x_2845_ = lean_st_ref_get(v___y_2838_);
v_snd_2846_ = lean_ctor_get(v_b_2837_, 1);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_b_2837_);
if (v_isSharedCheck_3011_ == 0)
{
lean_object* v_unused_3012_; 
v_unused_3012_ = lean_ctor_get(v_b_2837_, 0);
lean_dec(v_unused_3012_);
v___x_2848_ = v_b_2837_;
v_isShared_2849_ = v_isSharedCheck_3011_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_snd_2846_);
lean_dec(v_b_2837_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_3011_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; 
lean_inc(v_snd_2846_);
v___x_2850_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2845_, v_snd_2846_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___x_2845_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_3002_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_3002_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_3002_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v_self_2855_; lean_object* v_next_2856_; lean_object* v_congr_2857_; lean_object* v_target_x3f_2858_; lean_object* v_proof_x3f_2859_; uint8_t v_flipped_2860_; lean_object* v_size_2861_; uint8_t v_interpreted_2862_; uint8_t v_ctor_2863_; uint8_t v_hasLambdas_2864_; uint8_t v_heqProofs_2865_; lean_object* v_idx_2866_; lean_object* v_generation_2867_; lean_object* v_mt_2868_; lean_object* v_sTerms_2869_; uint8_t v_funCC_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_3000_; 
v_self_2855_ = lean_ctor_get(v_a_2851_, 0);
v_next_2856_ = lean_ctor_get(v_a_2851_, 1);
v_congr_2857_ = lean_ctor_get(v_a_2851_, 3);
v_target_x3f_2858_ = lean_ctor_get(v_a_2851_, 4);
v_proof_x3f_2859_ = lean_ctor_get(v_a_2851_, 5);
v_flipped_2860_ = lean_ctor_get_uint8(v_a_2851_, sizeof(void*)*11);
v_size_2861_ = lean_ctor_get(v_a_2851_, 6);
v_interpreted_2862_ = lean_ctor_get_uint8(v_a_2851_, sizeof(void*)*11 + 1);
v_ctor_2863_ = lean_ctor_get_uint8(v_a_2851_, sizeof(void*)*11 + 2);
v_hasLambdas_2864_ = lean_ctor_get_uint8(v_a_2851_, sizeof(void*)*11 + 3);
v_heqProofs_2865_ = lean_ctor_get_uint8(v_a_2851_, sizeof(void*)*11 + 4);
v_idx_2866_ = lean_ctor_get(v_a_2851_, 7);
v_generation_2867_ = lean_ctor_get(v_a_2851_, 8);
v_mt_2868_ = lean_ctor_get(v_a_2851_, 9);
v_sTerms_2869_ = lean_ctor_get(v_a_2851_, 10);
v_funCC_2870_ = lean_ctor_get_uint8(v_a_2851_, sizeof(void*)*11 + 5);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_a_2851_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v_a_2851_, 2);
lean_dec(v_unused_3001_);
v___x_2872_ = v_a_2851_;
v_isShared_2873_ = v_isSharedCheck_3000_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_sTerms_2869_);
lean_inc(v_mt_2868_);
lean_inc(v_generation_2867_);
lean_inc(v_idx_2866_);
lean_inc(v_size_2861_);
lean_inc(v_proof_x3f_2859_);
lean_inc(v_target_x3f_2858_);
lean_inc(v_congr_2857_);
lean_inc(v_next_2856_);
lean_inc(v_self_2855_);
lean_dec(v_a_2851_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_3000_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; lean_object* v___y_2889_; lean_object* v___x_2899_; 
v___x_2874_ = lean_box(0);
lean_inc(v_sTerms_2869_);
lean_inc(v_mt_2868_);
lean_inc(v_generation_2867_);
lean_inc(v_idx_2866_);
lean_inc(v_size_2861_);
lean_inc(v_proof_x3f_2859_);
lean_inc(v_target_x3f_2858_);
lean_inc_ref(v_rootNew_2835_);
lean_inc_ref(v_next_2856_);
lean_inc_ref(v_self_2855_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 2, v_rootNew_2835_);
v___x_2899_ = v___x_2872_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_self_2855_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_next_2856_);
lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_rootNew_2835_);
lean_ctor_set(v_reuseFailAlloc_2999_, 3, v_congr_2857_);
lean_ctor_set(v_reuseFailAlloc_2999_, 4, v_target_x3f_2858_);
lean_ctor_set(v_reuseFailAlloc_2999_, 5, v_proof_x3f_2859_);
lean_ctor_set(v_reuseFailAlloc_2999_, 6, v_size_2861_);
lean_ctor_set(v_reuseFailAlloc_2999_, 7, v_idx_2866_);
lean_ctor_set(v_reuseFailAlloc_2999_, 8, v_generation_2867_);
lean_ctor_set(v_reuseFailAlloc_2999_, 9, v_mt_2868_);
lean_ctor_set(v_reuseFailAlloc_2999_, 10, v_sTerms_2869_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*11, v_flipped_2860_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*11 + 1, v_interpreted_2862_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*11 + 2, v_ctor_2863_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*11 + 3, v_hasLambdas_2864_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*11 + 4, v_heqProofs_2865_);
lean_ctor_set_uint8(v_reuseFailAlloc_2999_, sizeof(void*)*11 + 5, v_funCC_2870_);
v___x_2899_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2898_;
}
v___jp_2875_:
{
uint8_t v___x_2876_; 
v___x_2876_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_2856_, v_lhs_2834_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2878_; 
lean_del_object(v___x_2853_);
lean_dec(v_snd_2846_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 1, v_next_2856_);
lean_ctor_set(v___x_2848_, 0, v___x_2874_);
v___x_2878_ = v___x_2848_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_next_2856_);
v___x_2878_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
v_b_2837_ = v___x_2878_;
goto _start;
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
lean_dec_ref(v_next_2856_);
lean_dec_ref(v_rootNew_2835_);
v___x_2881_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2881_);
v___x_2883_ = v___x_2848_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_snd_2846_);
v___x_2883_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2885_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2883_);
v___x_2885_ = v___x_2853_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
v___jp_2888_:
{
if (lean_obj_tag(v___y_2889_) == 0)
{
lean_dec_ref(v___y_2889_);
goto v___jp_2875_;
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec_ref(v_next_2856_);
lean_del_object(v___x_2853_);
lean_del_object(v___x_2848_);
lean_dec(v_snd_2846_);
lean_dec_ref(v_rootNew_2835_);
v_a_2890_ = lean_ctor_get(v___y_2889_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___y_2889_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___y_2889_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___y_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; 
lean_inc_ref(v___x_2899_);
lean_inc_ref(v_self_2855_);
v___x_2900_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2855_, v___x_2899_, v___y_2838_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_dec_ref(v___x_2900_);
if (v_a_2836_ == 0)
{
lean_dec_ref(v___x_2899_);
lean_dec(v_sTerms_2869_);
lean_dec(v_mt_2868_);
lean_dec(v_generation_2867_);
lean_dec(v_idx_2866_);
lean_dec(v_size_2861_);
lean_dec(v_proof_x3f_2859_);
lean_dec(v_target_x3f_2858_);
lean_dec_ref(v_self_2855_);
goto v___jp_2875_;
}
else
{
lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2901_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2902_ = lean_unsigned_to_nat(3u);
v___x_2903_ = l_Lean_Expr_isAppOfArity(v_self_2855_, v___x_2901_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_dec_ref(v___x_2899_);
lean_dec(v_sTerms_2869_);
lean_dec(v_mt_2868_);
lean_dec(v_generation_2867_);
lean_dec(v_idx_2866_);
lean_dec(v_size_2861_);
lean_dec(v_proof_x3f_2859_);
lean_dec(v_target_x3f_2858_);
lean_dec_ref(v_self_2855_);
goto v___jp_2875_;
}
else
{
uint8_t v___x_2904_; 
v___x_2904_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2899_);
lean_dec_ref(v___x_2899_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; lean_object* v_toGoalState_2906_; lean_object* v_enodeMap_2907_; lean_object* v_congrTable_2908_; lean_object* v___x_2909_; 
v___x_2905_ = lean_st_ref_get(v___y_2838_);
v_toGoalState_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_ref(v_toGoalState_2906_);
lean_dec(v___x_2905_);
v_enodeMap_2907_ = lean_ctor_get(v_toGoalState_2906_, 1);
lean_inc_ref(v_enodeMap_2907_);
v_congrTable_2908_ = lean_ctor_get(v_toGoalState_2906_, 4);
lean_inc_ref(v_congrTable_2908_);
lean_dec_ref(v_toGoalState_2906_);
lean_inc_ref(v_self_2855_);
v___x_2909_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_2907_, v_congrTable_2908_, v_self_2855_);
lean_dec_ref(v_congrTable_2908_);
lean_dec_ref(v_enodeMap_2907_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_dec(v_sTerms_2869_);
lean_dec(v_mt_2868_);
lean_dec(v_generation_2867_);
lean_dec(v_idx_2866_);
lean_dec(v_size_2861_);
lean_dec(v_proof_x3f_2859_);
lean_dec(v_target_x3f_2858_);
lean_dec_ref(v_self_2855_);
goto v___jp_2875_;
}
else
{
lean_object* v_val_2910_; lean_object* v_fst_2911_; lean_object* v___x_2912_; 
v_val_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_val_2910_);
lean_dec_ref(v___x_2909_);
v_fst_2911_ = lean_ctor_get(v_val_2910_, 0);
lean_inc(v_fst_2911_);
lean_dec(v_val_2910_);
v___x_2912_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_2911_, v___y_2839_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; uint8_t v___x_2914_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v___x_2912_);
v___x_2914_ = lean_unbox(v_a_2913_);
lean_dec(v_a_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2915_; lean_object* v_toGoalState_2916_; lean_object* v_mvarId_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2990_; 
v___x_2915_ = lean_st_ref_take(v___y_2838_);
v_toGoalState_2916_ = lean_ctor_get(v___x_2915_, 0);
v_mvarId_2917_ = lean_ctor_get(v___x_2915_, 1);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2919_ = v___x_2915_;
v_isShared_2920_ = v_isSharedCheck_2990_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_mvarId_2917_);
lean_inc(v_toGoalState_2916_);
lean_dec(v___x_2915_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2990_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v_nextDeclIdx_2921_; lean_object* v_enodeMap_2922_; lean_object* v_exprs_2923_; lean_object* v_parents_2924_; lean_object* v_congrTable_2925_; lean_object* v_appMap_2926_; lean_object* v_indicesFound_2927_; lean_object* v_newFacts_2928_; uint8_t v_inconsistent_2929_; lean_object* v_nextIdx_2930_; lean_object* v_newRawFacts_2931_; lean_object* v_facts_2932_; lean_object* v_extThms_2933_; lean_object* v_ematch_2934_; lean_object* v_inj_2935_; lean_object* v_split_2936_; lean_object* v_clean_2937_; lean_object* v_sstates_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2989_; 
v_nextDeclIdx_2921_ = lean_ctor_get(v_toGoalState_2916_, 0);
v_enodeMap_2922_ = lean_ctor_get(v_toGoalState_2916_, 1);
v_exprs_2923_ = lean_ctor_get(v_toGoalState_2916_, 2);
v_parents_2924_ = lean_ctor_get(v_toGoalState_2916_, 3);
v_congrTable_2925_ = lean_ctor_get(v_toGoalState_2916_, 4);
v_appMap_2926_ = lean_ctor_get(v_toGoalState_2916_, 5);
v_indicesFound_2927_ = lean_ctor_get(v_toGoalState_2916_, 6);
v_newFacts_2928_ = lean_ctor_get(v_toGoalState_2916_, 7);
v_inconsistent_2929_ = lean_ctor_get_uint8(v_toGoalState_2916_, sizeof(void*)*17);
v_nextIdx_2930_ = lean_ctor_get(v_toGoalState_2916_, 8);
v_newRawFacts_2931_ = lean_ctor_get(v_toGoalState_2916_, 9);
v_facts_2932_ = lean_ctor_get(v_toGoalState_2916_, 10);
v_extThms_2933_ = lean_ctor_get(v_toGoalState_2916_, 11);
v_ematch_2934_ = lean_ctor_get(v_toGoalState_2916_, 12);
v_inj_2935_ = lean_ctor_get(v_toGoalState_2916_, 13);
v_split_2936_ = lean_ctor_get(v_toGoalState_2916_, 14);
v_clean_2937_ = lean_ctor_get(v_toGoalState_2916_, 15);
v_sstates_2938_ = lean_ctor_get(v_toGoalState_2916_, 16);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_toGoalState_2916_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2940_ = v_toGoalState_2916_;
v_isShared_2941_ = v_isSharedCheck_2989_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_sstates_2938_);
lean_inc(v_clean_2937_);
lean_inc(v_split_2936_);
lean_inc(v_inj_2935_);
lean_inc(v_ematch_2934_);
lean_inc(v_extThms_2933_);
lean_inc(v_facts_2932_);
lean_inc(v_newRawFacts_2931_);
lean_inc(v_nextIdx_2930_);
lean_inc(v_newFacts_2928_);
lean_inc(v_indicesFound_2927_);
lean_inc(v_appMap_2926_);
lean_inc(v_congrTable_2925_);
lean_inc(v_parents_2924_);
lean_inc(v_exprs_2923_);
lean_inc(v_enodeMap_2922_);
lean_inc(v_nextDeclIdx_2921_);
lean_dec(v_toGoalState_2916_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2989_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2942_ = lean_box(0);
lean_inc_ref(v_self_2855_);
v___x_2943_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_2922_, v_congrTable_2925_, v_self_2855_, v___x_2942_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_2943_);
v___x_2945_ = v___x_2940_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_nextDeclIdx_2921_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_enodeMap_2922_);
lean_ctor_set(v_reuseFailAlloc_2988_, 2, v_exprs_2923_);
lean_ctor_set(v_reuseFailAlloc_2988_, 3, v_parents_2924_);
lean_ctor_set(v_reuseFailAlloc_2988_, 4, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_2988_, 5, v_appMap_2926_);
lean_ctor_set(v_reuseFailAlloc_2988_, 6, v_indicesFound_2927_);
lean_ctor_set(v_reuseFailAlloc_2988_, 7, v_newFacts_2928_);
lean_ctor_set(v_reuseFailAlloc_2988_, 8, v_nextIdx_2930_);
lean_ctor_set(v_reuseFailAlloc_2988_, 9, v_newRawFacts_2931_);
lean_ctor_set(v_reuseFailAlloc_2988_, 10, v_facts_2932_);
lean_ctor_set(v_reuseFailAlloc_2988_, 11, v_extThms_2933_);
lean_ctor_set(v_reuseFailAlloc_2988_, 12, v_ematch_2934_);
lean_ctor_set(v_reuseFailAlloc_2988_, 13, v_inj_2935_);
lean_ctor_set(v_reuseFailAlloc_2988_, 14, v_split_2936_);
lean_ctor_set(v_reuseFailAlloc_2988_, 15, v_clean_2937_);
lean_ctor_set(v_reuseFailAlloc_2988_, 16, v_sstates_2938_);
lean_ctor_set_uint8(v_reuseFailAlloc_2988_, sizeof(void*)*17, v_inconsistent_2929_);
v___x_2945_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2947_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2945_);
v___x_2947_ = v___x_2919_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_mvarId_2917_);
v___x_2947_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_st_ref_set(v___y_2838_, v___x_2947_);
lean_inc_ref(v_rootNew_2835_);
lean_inc_ref(v_next_2856_);
lean_inc_ref_n(v_self_2855_, 3);
v___x_2949_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v___x_2949_, 0, v_self_2855_);
lean_ctor_set(v___x_2949_, 1, v_next_2856_);
lean_ctor_set(v___x_2949_, 2, v_rootNew_2835_);
lean_ctor_set(v___x_2949_, 3, v_self_2855_);
lean_ctor_set(v___x_2949_, 4, v_target_x3f_2858_);
lean_ctor_set(v___x_2949_, 5, v_proof_x3f_2859_);
lean_ctor_set(v___x_2949_, 6, v_size_2861_);
lean_ctor_set(v___x_2949_, 7, v_idx_2866_);
lean_ctor_set(v___x_2949_, 8, v_generation_2867_);
lean_ctor_set(v___x_2949_, 9, v_mt_2868_);
lean_ctor_set(v___x_2949_, 10, v_sTerms_2869_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*11, v_flipped_2860_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*11 + 1, v_interpreted_2862_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*11 + 2, v_ctor_2863_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*11 + 3, v_hasLambdas_2864_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*11 + 4, v_heqProofs_2865_);
lean_ctor_set_uint8(v___x_2949_, sizeof(void*)*11 + 5, v_funCC_2870_);
v___x_2950_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2855_, v___x_2949_, v___y_2838_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
lean_dec_ref(v___x_2950_);
v___x_2951_ = lean_st_ref_get(v___y_2838_);
lean_inc(v_fst_2911_);
v___x_2952_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2951_, v_fst_2911_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___x_2951_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v_self_2954_; lean_object* v_next_2955_; lean_object* v_root_2956_; lean_object* v_target_x3f_2957_; lean_object* v_proof_x3f_2958_; uint8_t v_flipped_2959_; lean_object* v_size_2960_; uint8_t v_interpreted_2961_; uint8_t v_ctor_2962_; uint8_t v_hasLambdas_2963_; uint8_t v_heqProofs_2964_; lean_object* v_idx_2965_; lean_object* v_generation_2966_; lean_object* v_mt_2967_; lean_object* v_sTerms_2968_; uint8_t v_funCC_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2977_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref(v___x_2952_);
v_self_2954_ = lean_ctor_get(v_a_2953_, 0);
v_next_2955_ = lean_ctor_get(v_a_2953_, 1);
v_root_2956_ = lean_ctor_get(v_a_2953_, 2);
v_target_x3f_2957_ = lean_ctor_get(v_a_2953_, 4);
v_proof_x3f_2958_ = lean_ctor_get(v_a_2953_, 5);
v_flipped_2959_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*11);
v_size_2960_ = lean_ctor_get(v_a_2953_, 6);
v_interpreted_2961_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*11 + 1);
v_ctor_2962_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*11 + 2);
v_hasLambdas_2963_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*11 + 3);
v_heqProofs_2964_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*11 + 4);
v_idx_2965_ = lean_ctor_get(v_a_2953_, 7);
v_generation_2966_ = lean_ctor_get(v_a_2953_, 8);
v_mt_2967_ = lean_ctor_get(v_a_2953_, 9);
v_sTerms_2968_ = lean_ctor_get(v_a_2953_, 10);
v_funCC_2969_ = lean_ctor_get_uint8(v_a_2953_, sizeof(void*)*11 + 5);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_a_2953_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v_a_2953_, 3);
lean_dec(v_unused_2978_);
v___x_2971_ = v_a_2953_;
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_sTerms_2968_);
lean_inc(v_mt_2967_);
lean_inc(v_generation_2966_);
lean_inc(v_idx_2965_);
lean_inc(v_size_2960_);
lean_inc(v_proof_x3f_2958_);
lean_inc(v_target_x3f_2957_);
lean_inc(v_root_2956_);
lean_inc(v_next_2955_);
lean_inc(v_self_2954_);
lean_dec(v_a_2953_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 3, v_self_2855_);
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_self_2954_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_next_2955_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_root_2956_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_self_2855_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_target_x3f_2957_);
lean_ctor_set(v_reuseFailAlloc_2976_, 5, v_proof_x3f_2958_);
lean_ctor_set(v_reuseFailAlloc_2976_, 6, v_size_2960_);
lean_ctor_set(v_reuseFailAlloc_2976_, 7, v_idx_2965_);
lean_ctor_set(v_reuseFailAlloc_2976_, 8, v_generation_2966_);
lean_ctor_set(v_reuseFailAlloc_2976_, 9, v_mt_2967_);
lean_ctor_set(v_reuseFailAlloc_2976_, 10, v_sTerms_2968_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*11, v_flipped_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*11 + 1, v_interpreted_2961_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*11 + 2, v_ctor_2962_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*11 + 3, v_hasLambdas_2963_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*11 + 4, v_heqProofs_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*11 + 5, v_funCC_2969_);
v___x_2974_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_2911_, v___x_2974_, v___y_2838_);
v___y_2889_ = v___x_2975_;
goto v___jp_2888_;
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v_fst_2911_);
lean_dec_ref(v_next_2856_);
lean_dec_ref(v_self_2855_);
lean_del_object(v___x_2853_);
lean_del_object(v___x_2848_);
lean_dec(v_snd_2846_);
lean_dec_ref(v_rootNew_2835_);
v_a_2979_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2952_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2952_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
else
{
lean_dec(v_fst_2911_);
lean_dec_ref(v_self_2855_);
v___y_2889_ = v___x_2950_;
goto v___jp_2888_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2911_);
lean_dec(v_sTerms_2869_);
lean_dec(v_mt_2868_);
lean_dec(v_generation_2867_);
lean_dec(v_idx_2866_);
lean_dec(v_size_2861_);
lean_dec(v_proof_x3f_2859_);
lean_dec(v_target_x3f_2858_);
lean_dec_ref(v_self_2855_);
goto v___jp_2875_;
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec(v_fst_2911_);
lean_dec(v_sTerms_2869_);
lean_dec(v_mt_2868_);
lean_dec(v_generation_2867_);
lean_dec(v_idx_2866_);
lean_dec(v_size_2861_);
lean_dec(v_proof_x3f_2859_);
lean_dec(v_target_x3f_2858_);
lean_dec_ref(v_next_2856_);
lean_dec_ref(v_self_2855_);
lean_del_object(v___x_2853_);
lean_del_object(v___x_2848_);
lean_dec(v_snd_2846_);
lean_dec_ref(v_rootNew_2835_);
v_a_2991_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2912_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2912_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
}
else
{
lean_dec(v_sTerms_2869_);
lean_dec(v_mt_2868_);
lean_dec(v_generation_2867_);
lean_dec(v_idx_2866_);
lean_dec(v_size_2861_);
lean_dec(v_proof_x3f_2859_);
lean_dec(v_target_x3f_2858_);
lean_dec_ref(v_self_2855_);
goto v___jp_2875_;
}
}
}
}
else
{
lean_dec_ref(v___x_2899_);
lean_dec(v_sTerms_2869_);
lean_dec(v_mt_2868_);
lean_dec(v_generation_2867_);
lean_dec(v_idx_2866_);
lean_dec(v_size_2861_);
lean_dec(v_proof_x3f_2859_);
lean_dec(v_target_x3f_2858_);
lean_dec_ref(v_self_2855_);
v___y_2889_ = v___x_2900_;
goto v___jp_2888_;
}
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_del_object(v___x_2848_);
lean_dec(v_snd_2846_);
lean_dec_ref(v_rootNew_2835_);
v_a_3003_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2850_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2850_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3013_, lean_object* v_rootNew_3014_, lean_object* v_a_3015_, lean_object* v_b_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
uint8_t v_a_27767__boxed_3024_; lean_object* v_res_3025_; 
v_a_27767__boxed_3024_ = lean_unbox(v_a_3015_);
v_res_3025_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3013_, v_rootNew_3014_, v_a_27767__boxed_3024_, v_b_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v_lhs_3013_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3026_, lean_object* v_rootNew_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3027_, v_a_3032_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; lean_object* v___x_3044_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref(v___x_3039_);
v___x_3041_ = lean_box(0);
lean_inc_ref(v_lhs_3026_);
v___x_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3041_);
lean_ctor_set(v___x_3042_, 1, v_lhs_3026_);
v___x_3043_ = lean_unbox(v_a_3040_);
lean_dec(v_a_3040_);
v___x_3044_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3026_, v_rootNew_3027_, v___x_3043_, v___x_3042_, v_a_3028_, v_a_3032_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
lean_dec_ref(v_lhs_3026_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3058_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3058_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3058_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v_fst_3049_; 
v_fst_3049_ = lean_ctor_get(v_a_3045_, 0);
lean_inc(v_fst_3049_);
lean_dec(v_a_3045_);
if (lean_obj_tag(v_fst_3049_) == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3050_ = lean_box(0);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3050_);
v___x_3052_ = v___x_3047_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
else
{
lean_object* v_val_3054_; lean_object* v___x_3056_; 
v_val_3054_ = lean_ctor_get(v_fst_3049_, 0);
lean_inc(v_val_3054_);
lean_dec_ref(v_fst_3049_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v_val_3054_);
v___x_3056_ = v___x_3047_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_val_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
v_a_3059_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3044_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3044_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v_rootNew_3027_);
lean_dec_ref(v_lhs_3026_);
v_a_3067_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3039_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3039_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3075_, lean_object* v_rootNew_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3075_, v_rootNew_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
lean_dec(v_a_3078_);
lean_dec(v_a_3077_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3089_, lean_object* v_00_u03b2_3090_, lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3089_, v_x_3091_, v_x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3094_, lean_object* v_00_u03b2_3095_, lean_object* v_x_3096_, lean_object* v_x_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3094_, v_00_u03b2_3095_, v_x_3096_, v_x_3097_);
lean_dec_ref(v_x_3096_);
lean_dec_ref(v___x_3094_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3099_, lean_object* v_00_u03b2_3100_, lean_object* v_x_3101_, lean_object* v_x_3102_, lean_object* v_x_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3099_, v_x_3101_, v_x_3102_, v_x_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3105_, lean_object* v_00_u03b2_3106_, lean_object* v_x_3107_, lean_object* v_x_3108_, lean_object* v_x_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3105_, v_00_u03b2_3106_, v_x_3107_, v_x_3108_, v_x_3109_);
lean_dec_ref(v___x_3105_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3111_, lean_object* v_rootNew_3112_, uint8_t v_a_3113_, lean_object* v_b_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3111_, v_rootNew_3112_, v_a_3113_, v_b_3114_, v___y_3115_, v___y_3119_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3127_, lean_object* v_rootNew_3128_, lean_object* v_a_3129_, lean_object* v_b_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v_a_28122__boxed_3142_; lean_object* v_res_3143_; 
v_a_28122__boxed_3142_ = lean_unbox(v_a_3129_);
v_res_3143_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3127_, v_rootNew_3128_, v_a_28122__boxed_3142_, v_b_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v_lhs_3127_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3144_, lean_object* v_00_u03b2_3145_, lean_object* v_x_3146_, size_t v_x_3147_, lean_object* v_x_3148_){
_start:
{
lean_object* v___x_3149_; 
lean_inc_ref(v_x_3146_);
v___x_3149_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3144_, v_x_3146_, v_x_3147_, v_x_3148_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3150_, lean_object* v_00_u03b2_3151_, lean_object* v_x_3152_, lean_object* v_x_3153_, lean_object* v_x_3154_){
_start:
{
size_t v_x_28162__boxed_3155_; lean_object* v_res_3156_; 
v_x_28162__boxed_3155_ = lean_unbox_usize(v_x_3153_);
lean_dec(v_x_3153_);
v_res_3156_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3150_, v_00_u03b2_3151_, v_x_3152_, v_x_28162__boxed_3155_, v_x_3154_);
lean_dec_ref(v_x_3152_);
lean_dec_ref(v___x_3150_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3157_, lean_object* v_00_u03b2_3158_, lean_object* v_x_3159_, size_t v_x_3160_, size_t v_x_3161_, lean_object* v_x_3162_, lean_object* v_x_3163_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3157_, v_x_3159_, v_x_3160_, v_x_3161_, v_x_3162_, v_x_3163_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3165_, lean_object* v_00_u03b2_3166_, lean_object* v_x_3167_, lean_object* v_x_3168_, lean_object* v_x_3169_, lean_object* v_x_3170_, lean_object* v_x_3171_){
_start:
{
size_t v_x_28176__boxed_3172_; size_t v_x_28177__boxed_3173_; lean_object* v_res_3174_; 
v_x_28176__boxed_3172_ = lean_unbox_usize(v_x_3168_);
lean_dec(v_x_3168_);
v_x_28177__boxed_3173_ = lean_unbox_usize(v_x_3169_);
lean_dec(v_x_3169_);
v_res_3174_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3165_, v_00_u03b2_3166_, v_x_3167_, v_x_28176__boxed_3172_, v_x_28177__boxed_3173_, v_x_3170_, v_x_3171_);
lean_dec_ref(v___x_3165_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3175_, lean_object* v_00_u03b2_3176_, lean_object* v_keys_3177_, lean_object* v_vals_3178_, lean_object* v_heq_3179_, lean_object* v_i_3180_, lean_object* v_k_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3175_, v_keys_3177_, v_vals_3178_, v_i_3180_, v_k_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3183_, lean_object* v_00_u03b2_3184_, lean_object* v_keys_3185_, lean_object* v_vals_3186_, lean_object* v_heq_3187_, lean_object* v_i_3188_, lean_object* v_k_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3183_, v_00_u03b2_3184_, v_keys_3185_, v_vals_3186_, v_heq_3187_, v_i_3188_, v_k_3189_);
lean_dec_ref(v_vals_3186_);
lean_dec_ref(v_keys_3185_);
lean_dec_ref(v___x_3183_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3191_, lean_object* v_00_u03b2_3192_, lean_object* v_n_3193_, lean_object* v_k_3194_, lean_object* v_v_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3191_, v_n_3193_, v_k_3194_, v_v_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3197_, lean_object* v_00_u03b2_3198_, lean_object* v_n_3199_, lean_object* v_k_3200_, lean_object* v_v_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3197_, v_00_u03b2_3198_, v_n_3199_, v_k_3200_, v_v_3201_);
lean_dec_ref(v___x_3197_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3203_, lean_object* v_00_u03b2_3204_, size_t v_depth_3205_, lean_object* v_keys_3206_, lean_object* v_vals_3207_, lean_object* v_heq_3208_, lean_object* v_i_3209_, lean_object* v_entries_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3203_, v_depth_3205_, v_keys_3206_, v_vals_3207_, v_i_3209_, v_entries_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3212_, lean_object* v_00_u03b2_3213_, lean_object* v_depth_3214_, lean_object* v_keys_3215_, lean_object* v_vals_3216_, lean_object* v_heq_3217_, lean_object* v_i_3218_, lean_object* v_entries_3219_){
_start:
{
size_t v_depth_boxed_3220_; lean_object* v_res_3221_; 
v_depth_boxed_3220_ = lean_unbox_usize(v_depth_3214_);
lean_dec(v_depth_3214_);
v_res_3221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3212_, v_00_u03b2_3213_, v_depth_boxed_3220_, v_keys_3215_, v_vals_3216_, v_heq_3217_, v_i_3218_, v_entries_3219_);
lean_dec_ref(v_vals_3216_);
lean_dec_ref(v_keys_3215_);
lean_dec_ref(v___x_3212_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3222_, lean_object* v_00_u03b2_3223_, lean_object* v_x_3224_, lean_object* v_x_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3222_, v_x_3224_, v_x_3225_, v_x_3226_, v_x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3229_, lean_object* v_00_u03b2_3230_, lean_object* v_x_3231_, lean_object* v_x_3232_, lean_object* v_x_3233_, lean_object* v_x_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3229_, v_00_u03b2_3230_, v_x_3231_, v_x_3232_, v_x_3233_, v_x_3234_);
lean_dec_ref(v___x_3229_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3236_, lean_object* v_b_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
if (lean_obj_tag(v_as_x27_3236_) == 0)
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v_b_3237_);
return v___x_3249_;
}
else
{
lean_object* v_head_3250_; lean_object* v_tail_3251_; lean_object* v___x_3252_; 
v_head_3250_ = lean_ctor_get(v_as_x27_3236_, 0);
v_tail_3251_ = lean_ctor_get(v_as_x27_3236_, 1);
lean_inc(v_head_3250_);
v___x_3252_ = l_Lean_Meta_Grind_propagateUp(v_head_3250_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v___x_3253_; 
lean_dec_ref(v___x_3252_);
v___x_3253_ = lean_box(0);
v_as_x27_3236_ = v_tail_3251_;
v_b_3237_ = v___x_3253_;
goto _start;
}
else
{
return v___x_3252_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3255_, lean_object* v_b_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3255_, v_b_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
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
lean_dec(v_as_x27_3255_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3269_, lean_object* v_b_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
if (lean_obj_tag(v_as_x27_3269_) == 0)
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_b_3270_);
return v___x_3282_;
}
else
{
lean_object* v_head_3283_; lean_object* v_tail_3284_; lean_object* v___x_3285_; 
v_head_3283_ = lean_ctor_get(v_as_x27_3269_, 0);
v_tail_3284_ = lean_ctor_get(v_as_x27_3269_, 1);
lean_inc(v_head_3283_);
v___x_3285_ = l_Lean_Meta_Grind_propagateDown(v_head_3283_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v___x_3286_; 
lean_dec_ref(v___x_3285_);
v___x_3286_ = lean_box(0);
v_as_x27_3269_ = v_tail_3284_;
v_b_3270_ = v___x_3286_;
goto _start;
}
else
{
return v___x_3285_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3288_, lean_object* v_b_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3288_, v_b_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec(v_as_x27_3288_);
return v_res_3301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_cls_3305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3306_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3307_ = l_Lean_Name_append(v___x_3306_, v_cls_3305_);
return v___x_3307_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
return v___x_3313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3316_ = l_Lean_stringToMessageData(v___x_3315_);
return v___x_3316_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3319_ = l_Lean_stringToMessageData(v___x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3320_, uint8_t v_isHEq_3321_, lean_object* v_lhs_3322_, lean_object* v_rhs_3323_, lean_object* v_lhsNode_3324_, lean_object* v_rhsNode_3325_, lean_object* v_lhsRoot_3326_, lean_object* v_rhsRoot_3327_, uint8_t v_flipped_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; uint8_t v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; uint8_t v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; uint8_t v___y_3420_; uint8_t v___y_3421_; lean_object* v___y_3422_; uint8_t v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; uint8_t v___y_3427_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; uint8_t v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; uint8_t v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; uint8_t v___y_3483_; lean_object* v___y_3484_; uint8_t v___y_3485_; uint8_t v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; uint8_t v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; uint8_t v___y_3492_; uint8_t v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; uint8_t v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v_options_3574_; lean_object* v_inheritedTraceOptions_3575_; uint8_t v_hasTrace_3576_; lean_object* v_cls_3577_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v_fns_u2082_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v_fns_u2081_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; 
v_options_3574_ = lean_ctor_get(v_a_3337_, 2);
v_inheritedTraceOptions_3575_ = lean_ctor_get(v_a_3337_, 13);
v_hasTrace_3576_ = lean_ctor_get_uint8(v_options_3574_, sizeof(void*)*1);
v_cls_3577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3576_ == 0)
{
v___y_3696_ = v_a_3329_;
v___y_3697_ = v_a_3330_;
v___y_3698_ = v_a_3331_;
v___y_3699_ = v_a_3332_;
v___y_3700_ = v_a_3333_;
v___y_3701_ = v_a_3334_;
v___y_3702_ = v_a_3335_;
v___y_3703_ = v_a_3336_;
v___y_3704_ = v_a_3337_;
v___y_3705_ = v_a_3338_;
goto v___jp_3695_;
}
else
{
lean_object* v___x_3775_; uint8_t v___x_3776_; 
v___x_3775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3776_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3575_, v_options_3574_, v___x_3775_);
if (v___x_3776_ == 0)
{
v___y_3696_ = v_a_3329_;
v___y_3697_ = v_a_3330_;
v___y_3698_ = v_a_3331_;
v___y_3699_ = v_a_3332_;
v___y_3700_ = v_a_3333_;
v___y_3701_ = v_a_3334_;
v___y_3702_ = v_a_3335_;
v___y_3703_ = v_a_3336_;
v___y_3704_ = v_a_3337_;
v___y_3705_ = v_a_3338_;
goto v___jp_3695_;
}
else
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_Meta_Grind_updateLastTag(v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v___x_3778_; 
lean_dec_ref(v___x_3777_);
lean_inc_ref(v_lhs_3322_);
v___x_3778_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3322_, v_a_3329_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3780_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___x_3778_);
lean_inc_ref(v_rhs_3323_);
v___x_3780_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3323_, v_a_3329_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref(v___x_3780_);
v___x_3782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
lean_ctor_set(v___x_3783_, 1, v_a_3779_);
v___x_3784_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3783_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
lean_ctor_set(v___x_3786_, 1, v_a_3781_);
v___x_3787_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3577_, v___x_3786_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_dec_ref(v___x_3787_);
v___y_3696_ = v_a_3329_;
v___y_3697_ = v_a_3330_;
v___y_3698_ = v_a_3331_;
v___y_3699_ = v_a_3332_;
v___y_3700_ = v_a_3333_;
v___y_3701_ = v_a_3334_;
v___y_3702_ = v_a_3335_;
v___y_3703_ = v_a_3336_;
v___y_3704_ = v_a_3337_;
v___y_3705_ = v_a_3338_;
goto v___jp_3695_;
}
else
{
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhsNode_3324_);
lean_dec_ref(v_rhs_3323_);
lean_dec_ref(v_lhs_3322_);
lean_dec_ref(v_proof_3320_);
return v___x_3787_;
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec(v_a_3779_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhsNode_3324_);
lean_dec_ref(v_rhs_3323_);
lean_dec_ref(v_lhs_3322_);
lean_dec_ref(v_proof_3320_);
v_a_3788_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3780_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3780_);
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
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhsNode_3324_);
lean_dec_ref(v_rhs_3323_);
lean_dec_ref(v_lhs_3322_);
lean_dec_ref(v_proof_3320_);
v_a_3796_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3778_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3778_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhsNode_3324_);
lean_dec_ref(v_rhs_3323_);
lean_dec_ref(v_lhs_3322_);
lean_dec_ref(v_proof_3320_);
return v___x_3777_;
}
}
}
v___jp_3340_:
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3347_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3383_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3383_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3383_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
uint8_t v___x_3362_; 
v___x_3362_ = lean_unbox(v_a_3358_);
lean_dec(v_a_3358_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_del_object(v___x_3360_);
v___x_3363_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3343_);
lean_dec(v___y_3343_);
v___x_3364_ = lean_box(0);
v___x_3365_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3363_, v___x_3364_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___x_3363_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3366_; 
lean_dec_ref(v___x_3365_);
v___x_3366_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3346_, v___x_3364_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3367_; 
lean_dec_ref(v___x_3366_);
v___x_3367_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3345_, v___y_3341_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec_ref(v___y_3341_);
lean_dec_ref(v___y_3345_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v___x_3368_; 
lean_dec_ref(v___x_3367_);
v___x_3368_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3342_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3377_; 
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3377_ == 0)
{
lean_object* v_unused_3378_; 
v_unused_3378_ = lean_ctor_get(v___x_3368_, 0);
lean_dec(v_unused_3378_);
v___x_3370_ = v___x_3368_;
v_isShared_3371_ = v_isSharedCheck_3377_;
goto v_resetjp_3369_;
}
else
{
lean_dec(v___x_3368_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3377_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
uint8_t v___x_3372_; 
v___x_3372_ = l_Lean_Expr_isTrue(v___y_3344_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3374_; 
lean_dec(v___y_3346_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3364_);
v___x_3374_ = v___x_3370_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3364_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
else
{
lean_object* v___x_3376_; 
lean_del_object(v___x_3370_);
v___x_3376_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3346_);
return v___x_3376_;
}
}
}
else
{
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3344_);
return v___x_3368_;
}
}
else
{
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3342_);
return v___x_3367_;
}
}
else
{
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
return v___x_3366_;
}
}
else
{
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
return v___x_3365_;
}
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3381_; 
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
v___x_3379_ = lean_box(0);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v___x_3379_);
v___x_3381_ = v___x_3360_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
v_a_3384_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3357_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3357_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
v___jp_3392_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_inc_ref(v___y_3401_);
v___x_3428_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v___x_3428_, 0, v___y_3401_);
lean_ctor_set(v___x_3428_, 1, v___y_3394_);
lean_ctor_set(v___x_3428_, 2, v___y_3419_);
lean_ctor_set(v___x_3428_, 3, v___y_3414_);
lean_ctor_set(v___x_3428_, 4, v___y_3422_);
lean_ctor_set(v___x_3428_, 5, v___y_3395_);
lean_ctor_set(v___x_3428_, 6, v___y_3413_);
lean_ctor_set(v___x_3428_, 7, v___y_3418_);
lean_ctor_set(v___x_3428_, 8, v___y_3409_);
lean_ctor_set(v___x_3428_, 9, v___y_3416_);
lean_ctor_set(v___x_3428_, 10, v___y_3411_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*11, v___y_3421_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*11 + 1, v___y_3423_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*11 + 2, v___y_3406_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*11 + 3, v___y_3412_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*11 + 4, v___y_3427_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*11 + 5, v___y_3420_);
lean_inc_ref(v___y_3417_);
v___x_3429_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3417_, v___x_3428_, v___y_3424_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v___x_3430_; 
lean_dec_ref(v___x_3429_);
lean_inc_ref(v___y_3425_);
v___x_3430_ = l_Lean_Meta_Grind_propagateBeta(v___y_3425_, v___y_3410_, v___y_3424_, v___y_3407_, v___y_3405_, v___y_3397_, v___y_3399_, v___y_3404_, v___y_3403_, v___y_3426_, v___y_3402_, v___y_3408_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v___x_3431_; 
lean_dec_ref(v___x_3430_);
lean_inc_ref(v___y_3393_);
v___x_3431_ = l_Lean_Meta_Grind_propagateBeta(v___y_3393_, v___y_3398_, v___y_3424_, v___y_3407_, v___y_3405_, v___y_3397_, v___y_3399_, v___y_3404_, v___y_3403_, v___y_3426_, v___y_3402_, v___y_3408_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v___x_3432_; 
lean_dec_ref(v___x_3431_);
v___x_3432_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3327_, v_lhsRoot_3326_, v___y_3424_, v___y_3403_, v___y_3426_, v___y_3402_, v___y_3408_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3434_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref(v___x_3432_);
v___x_3434_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3415_, v___y_3424_);
lean_dec_ref(v___y_3415_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v___x_3435_; 
lean_dec_ref(v___x_3434_);
lean_inc_ref(v___y_3417_);
v___x_3435_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3396_, v___y_3417_, v___y_3424_, v___y_3407_, v___y_3405_, v___y_3397_, v___y_3399_, v___y_3404_, v___y_3403_, v___y_3426_, v___y_3402_, v___y_3408_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v___x_3436_; 
lean_dec_ref(v___x_3435_);
v___x_3436_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3424_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; uint8_t v___x_3438_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref(v___x_3436_);
v___x_3438_ = lean_unbox(v_a_3437_);
lean_dec(v_a_3437_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3401_, v___y_3424_, v___y_3407_, v___y_3405_, v___y_3397_, v___y_3399_, v___y_3404_, v___y_3403_, v___y_3426_, v___y_3402_, v___y_3408_);
lean_dec_ref(v___y_3401_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_dec_ref(v___x_3439_);
v___y_3341_ = v___y_3393_;
v___y_3342_ = v_a_3433_;
v___y_3343_ = v___y_3396_;
v___y_3344_ = v___y_3417_;
v___y_3345_ = v___y_3425_;
v___y_3346_ = v___y_3400_;
v___y_3347_ = v___y_3424_;
v___y_3348_ = v___y_3407_;
v___y_3349_ = v___y_3405_;
v___y_3350_ = v___y_3397_;
v___y_3351_ = v___y_3399_;
v___y_3352_ = v___y_3404_;
v___y_3353_ = v___y_3403_;
v___y_3354_ = v___y_3426_;
v___y_3355_ = v___y_3402_;
v___y_3356_ = v___y_3408_;
goto v___jp_3340_;
}
else
{
lean_dec(v_a_3433_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3400_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3393_);
return v___x_3439_;
}
}
else
{
lean_dec_ref(v___y_3401_);
v___y_3341_ = v___y_3393_;
v___y_3342_ = v_a_3433_;
v___y_3343_ = v___y_3396_;
v___y_3344_ = v___y_3417_;
v___y_3345_ = v___y_3425_;
v___y_3346_ = v___y_3400_;
v___y_3347_ = v___y_3424_;
v___y_3348_ = v___y_3407_;
v___y_3349_ = v___y_3405_;
v___y_3350_ = v___y_3397_;
v___y_3351_ = v___y_3399_;
v___y_3352_ = v___y_3404_;
v___y_3353_ = v___y_3403_;
v___y_3354_ = v___y_3426_;
v___y_3355_ = v___y_3402_;
v___y_3356_ = v___y_3408_;
goto v___jp_3340_;
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_a_3433_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3393_);
v_a_3440_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3436_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3436_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
else
{
lean_dec(v_a_3433_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3393_);
return v___x_3435_;
}
}
else
{
lean_dec(v_a_3433_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3393_);
return v___x_3434_;
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3455_; 
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3393_);
v_a_3448_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3450_ = v___x_3432_;
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3432_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3455_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
}
else
{
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
return v___x_3431_;
}
}
else
{
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
return v___x_3430_;
}
}
else
{
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v___y_3410_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
return v___x_3429_;
}
}
v___jp_3456_:
{
if (v_isHEq_3321_ == 0)
{
if (v___y_3475_ == 0)
{
v___y_3393_ = v___y_3458_;
v___y_3394_ = v___y_3457_;
v___y_3395_ = v___y_3459_;
v___y_3396_ = v___y_3460_;
v___y_3397_ = v___y_3461_;
v___y_3398_ = v___y_3462_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3464_;
v___y_3401_ = v___y_3465_;
v___y_3402_ = v___y_3466_;
v___y_3403_ = v___y_3467_;
v___y_3404_ = v___y_3469_;
v___y_3405_ = v___y_3468_;
v___y_3406_ = v___y_3470_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3472_;
v___y_3409_ = v___y_3473_;
v___y_3410_ = v___y_3474_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3492_;
v___y_3413_ = v___y_3477_;
v___y_3414_ = v___y_3478_;
v___y_3415_ = v___y_3479_;
v___y_3416_ = v___y_3480_;
v___y_3417_ = v___y_3481_;
v___y_3418_ = v___y_3482_;
v___y_3419_ = v___y_3484_;
v___y_3420_ = v___y_3483_;
v___y_3421_ = v___y_3485_;
v___y_3422_ = v___y_3487_;
v___y_3423_ = v___y_3489_;
v___y_3424_ = v___y_3488_;
v___y_3425_ = v___y_3490_;
v___y_3426_ = v___y_3491_;
v___y_3427_ = v___y_3486_;
goto v___jp_3392_;
}
else
{
v___y_3393_ = v___y_3458_;
v___y_3394_ = v___y_3457_;
v___y_3395_ = v___y_3459_;
v___y_3396_ = v___y_3460_;
v___y_3397_ = v___y_3461_;
v___y_3398_ = v___y_3462_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3464_;
v___y_3401_ = v___y_3465_;
v___y_3402_ = v___y_3466_;
v___y_3403_ = v___y_3467_;
v___y_3404_ = v___y_3469_;
v___y_3405_ = v___y_3468_;
v___y_3406_ = v___y_3470_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3472_;
v___y_3409_ = v___y_3473_;
v___y_3410_ = v___y_3474_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3492_;
v___y_3413_ = v___y_3477_;
v___y_3414_ = v___y_3478_;
v___y_3415_ = v___y_3479_;
v___y_3416_ = v___y_3480_;
v___y_3417_ = v___y_3481_;
v___y_3418_ = v___y_3482_;
v___y_3419_ = v___y_3484_;
v___y_3420_ = v___y_3483_;
v___y_3421_ = v___y_3485_;
v___y_3422_ = v___y_3487_;
v___y_3423_ = v___y_3489_;
v___y_3424_ = v___y_3488_;
v___y_3425_ = v___y_3490_;
v___y_3426_ = v___y_3491_;
v___y_3427_ = v___y_3475_;
goto v___jp_3392_;
}
}
else
{
v___y_3393_ = v___y_3458_;
v___y_3394_ = v___y_3457_;
v___y_3395_ = v___y_3459_;
v___y_3396_ = v___y_3460_;
v___y_3397_ = v___y_3461_;
v___y_3398_ = v___y_3462_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3464_;
v___y_3401_ = v___y_3465_;
v___y_3402_ = v___y_3466_;
v___y_3403_ = v___y_3467_;
v___y_3404_ = v___y_3469_;
v___y_3405_ = v___y_3468_;
v___y_3406_ = v___y_3470_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3472_;
v___y_3409_ = v___y_3473_;
v___y_3410_ = v___y_3474_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3492_;
v___y_3413_ = v___y_3477_;
v___y_3414_ = v___y_3478_;
v___y_3415_ = v___y_3479_;
v___y_3416_ = v___y_3480_;
v___y_3417_ = v___y_3481_;
v___y_3418_ = v___y_3482_;
v___y_3419_ = v___y_3484_;
v___y_3420_ = v___y_3483_;
v___y_3421_ = v___y_3485_;
v___y_3422_ = v___y_3487_;
v___y_3423_ = v___y_3489_;
v___y_3424_ = v___y_3488_;
v___y_3425_ = v___y_3490_;
v___y_3426_ = v___y_3491_;
v___y_3427_ = v_isHEq_3321_;
goto v___jp_3392_;
}
}
v___jp_3493_:
{
lean_object* v___x_3516_; 
v___x_3516_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3497_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_dec_ref(v___x_3516_);
v___x_3517_ = lean_st_ref_get(v___y_3506_);
v___x_3518_ = lean_st_ref_get(v___y_3506_);
lean_inc_ref(v___y_3498_);
v___x_3519_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3518_, v___y_3498_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec(v___x_3518_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v_self_3521_; lean_object* v_root_3522_; lean_object* v_congr_3523_; lean_object* v_target_x3f_3524_; lean_object* v_proof_x3f_3525_; uint8_t v_flipped_3526_; lean_object* v_size_3527_; uint8_t v_interpreted_3528_; uint8_t v_ctor_3529_; uint8_t v_hasLambdas_3530_; uint8_t v_heqProofs_3531_; lean_object* v_idx_3532_; lean_object* v_generation_3533_; lean_object* v_mt_3534_; lean_object* v_sTerms_3535_; uint8_t v_funCC_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3564_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref(v___x_3519_);
v_self_3521_ = lean_ctor_get(v_a_3520_, 0);
v_root_3522_ = lean_ctor_get(v_a_3520_, 2);
v_congr_3523_ = lean_ctor_get(v_a_3520_, 3);
v_target_x3f_3524_ = lean_ctor_get(v_a_3520_, 4);
v_proof_x3f_3525_ = lean_ctor_get(v_a_3520_, 5);
v_flipped_3526_ = lean_ctor_get_uint8(v_a_3520_, sizeof(void*)*11);
v_size_3527_ = lean_ctor_get(v_a_3520_, 6);
v_interpreted_3528_ = lean_ctor_get_uint8(v_a_3520_, sizeof(void*)*11 + 1);
v_ctor_3529_ = lean_ctor_get_uint8(v_a_3520_, sizeof(void*)*11 + 2);
v_hasLambdas_3530_ = lean_ctor_get_uint8(v_a_3520_, sizeof(void*)*11 + 3);
v_heqProofs_3531_ = lean_ctor_get_uint8(v_a_3520_, sizeof(void*)*11 + 4);
v_idx_3532_ = lean_ctor_get(v_a_3520_, 7);
v_generation_3533_ = lean_ctor_get(v_a_3520_, 8);
v_mt_3534_ = lean_ctor_get(v_a_3520_, 9);
v_sTerms_3535_ = lean_ctor_get(v_a_3520_, 10);
v_funCC_3536_ = lean_ctor_get_uint8(v_a_3520_, sizeof(void*)*11 + 5);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3564_ == 0)
{
lean_object* v_unused_3565_; 
v_unused_3565_ = lean_ctor_get(v_a_3520_, 1);
lean_dec(v_unused_3565_);
v___x_3538_ = v_a_3520_;
v_isShared_3539_ = v_isSharedCheck_3564_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_sTerms_3535_);
lean_inc(v_mt_3534_);
lean_inc(v_generation_3533_);
lean_inc(v_idx_3532_);
lean_inc(v_size_3527_);
lean_inc(v_proof_x3f_3525_);
lean_inc(v_target_x3f_3524_);
lean_inc(v_congr_3523_);
lean_inc(v_root_3522_);
lean_inc(v_self_3521_);
lean_dec(v_a_3520_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3564_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v_self_3540_; lean_object* v_next_3541_; lean_object* v_root_3542_; lean_object* v_congr_3543_; lean_object* v_target_x3f_3544_; lean_object* v_proof_x3f_3545_; uint8_t v_flipped_3546_; lean_object* v_size_3547_; uint8_t v_interpreted_3548_; uint8_t v_ctor_3549_; uint8_t v_hasLambdas_3550_; uint8_t v_heqProofs_3551_; lean_object* v_idx_3552_; lean_object* v_generation_3553_; lean_object* v_mt_3554_; lean_object* v_sTerms_3555_; uint8_t v_funCC_3556_; lean_object* v___x_3558_; 
v_self_3540_ = lean_ctor_get(v_rhsRoot_3327_, 0);
v_next_3541_ = lean_ctor_get(v_rhsRoot_3327_, 1);
v_root_3542_ = lean_ctor_get(v_rhsRoot_3327_, 2);
v_congr_3543_ = lean_ctor_get(v_rhsRoot_3327_, 3);
v_target_x3f_3544_ = lean_ctor_get(v_rhsRoot_3327_, 4);
v_proof_x3f_3545_ = lean_ctor_get(v_rhsRoot_3327_, 5);
v_flipped_3546_ = lean_ctor_get_uint8(v_rhsRoot_3327_, sizeof(void*)*11);
v_size_3547_ = lean_ctor_get(v_rhsRoot_3327_, 6);
v_interpreted_3548_ = lean_ctor_get_uint8(v_rhsRoot_3327_, sizeof(void*)*11 + 1);
v_ctor_3549_ = lean_ctor_get_uint8(v_rhsRoot_3327_, sizeof(void*)*11 + 2);
v_hasLambdas_3550_ = lean_ctor_get_uint8(v_rhsRoot_3327_, sizeof(void*)*11 + 3);
v_heqProofs_3551_ = lean_ctor_get_uint8(v_rhsRoot_3327_, sizeof(void*)*11 + 4);
v_idx_3552_ = lean_ctor_get(v_rhsRoot_3327_, 7);
v_generation_3553_ = lean_ctor_get(v_rhsRoot_3327_, 8);
v_mt_3554_ = lean_ctor_get(v_rhsRoot_3327_, 9);
v_sTerms_3555_ = lean_ctor_get(v_rhsRoot_3327_, 10);
v_funCC_3556_ = lean_ctor_get_uint8(v_rhsRoot_3327_, sizeof(void*)*11 + 5);
lean_inc_ref(v_next_3541_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 1, v_next_3541_);
v___x_3558_ = v___x_3538_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_self_3521_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_next_3541_);
lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_root_3522_);
lean_ctor_set(v_reuseFailAlloc_3563_, 3, v_congr_3523_);
lean_ctor_set(v_reuseFailAlloc_3563_, 4, v_target_x3f_3524_);
lean_ctor_set(v_reuseFailAlloc_3563_, 5, v_proof_x3f_3525_);
lean_ctor_set(v_reuseFailAlloc_3563_, 6, v_size_3527_);
lean_ctor_set(v_reuseFailAlloc_3563_, 7, v_idx_3532_);
lean_ctor_set(v_reuseFailAlloc_3563_, 8, v_generation_3533_);
lean_ctor_set(v_reuseFailAlloc_3563_, 9, v_mt_3534_);
lean_ctor_set(v_reuseFailAlloc_3563_, 10, v_sTerms_3535_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*11, v_flipped_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*11 + 1, v_interpreted_3528_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*11 + 2, v_ctor_3529_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*11 + 3, v_hasLambdas_3530_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*11 + 4, v_heqProofs_3531_);
lean_ctor_set_uint8(v_reuseFailAlloc_3563_, sizeof(void*)*11 + 5, v_funCC_3536_);
v___x_3558_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3502_, v___x_3558_, v___y_3506_);
if (lean_obj_tag(v___x_3559_) == 0)
{
uint8_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
lean_dec_ref(v___x_3559_);
v___x_3560_ = 0;
v___x_3561_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3517_, v_lhs_3322_, v___x_3560_);
lean_dec(v___x_3517_);
v___x_3562_ = lean_nat_add(v_size_3547_, v___y_3500_);
lean_dec(v___y_3500_);
if (v_hasLambdas_3550_ == 0)
{
lean_inc(v_target_x3f_3544_);
lean_inc_ref(v_root_3542_);
lean_inc(v_idx_3552_);
lean_inc(v_mt_3554_);
lean_inc_ref(v_congr_3543_);
lean_inc(v_sTerms_3555_);
lean_inc(v_generation_3553_);
lean_inc_ref(v_self_3540_);
lean_inc(v_proof_x3f_3545_);
v___y_3457_ = v___y_3496_;
v___y_3458_ = v___y_3495_;
v___y_3459_ = v_proof_x3f_3545_;
v___y_3460_ = v___y_3497_;
v___y_3461_ = v___y_3509_;
v___y_3462_ = v___y_3499_;
v___y_3463_ = v___y_3510_;
v___y_3464_ = v___x_3561_;
v___y_3465_ = v_self_3540_;
v___y_3466_ = v___y_3514_;
v___y_3467_ = v___y_3512_;
v___y_3468_ = v___y_3508_;
v___y_3469_ = v___y_3511_;
v___y_3470_ = v_ctor_3549_;
v___y_3471_ = v___y_3507_;
v___y_3472_ = v___y_3515_;
v___y_3473_ = v_generation_3553_;
v___y_3474_ = v___y_3505_;
v___y_3475_ = v_heqProofs_3551_;
v___y_3476_ = v_sTerms_3555_;
v___y_3477_ = v___x_3562_;
v___y_3478_ = v_congr_3543_;
v___y_3479_ = v___y_3498_;
v___y_3480_ = v_mt_3554_;
v___y_3481_ = v___y_3501_;
v___y_3482_ = v_idx_3552_;
v___y_3483_ = v_funCC_3556_;
v___y_3484_ = v_root_3542_;
v___y_3485_ = v_flipped_3546_;
v___y_3486_ = v___y_3494_;
v___y_3487_ = v_target_x3f_3544_;
v___y_3488_ = v___y_3506_;
v___y_3489_ = v_interpreted_3548_;
v___y_3490_ = v___y_3503_;
v___y_3491_ = v___y_3513_;
v___y_3492_ = v___y_3504_;
goto v___jp_3456_;
}
else
{
lean_inc(v_target_x3f_3544_);
lean_inc_ref(v_root_3542_);
lean_inc(v_idx_3552_);
lean_inc(v_mt_3554_);
lean_inc_ref(v_congr_3543_);
lean_inc(v_sTerms_3555_);
lean_inc(v_generation_3553_);
lean_inc_ref(v_self_3540_);
lean_inc(v_proof_x3f_3545_);
v___y_3457_ = v___y_3496_;
v___y_3458_ = v___y_3495_;
v___y_3459_ = v_proof_x3f_3545_;
v___y_3460_ = v___y_3497_;
v___y_3461_ = v___y_3509_;
v___y_3462_ = v___y_3499_;
v___y_3463_ = v___y_3510_;
v___y_3464_ = v___x_3561_;
v___y_3465_ = v_self_3540_;
v___y_3466_ = v___y_3514_;
v___y_3467_ = v___y_3512_;
v___y_3468_ = v___y_3508_;
v___y_3469_ = v___y_3511_;
v___y_3470_ = v_ctor_3549_;
v___y_3471_ = v___y_3507_;
v___y_3472_ = v___y_3515_;
v___y_3473_ = v_generation_3553_;
v___y_3474_ = v___y_3505_;
v___y_3475_ = v_heqProofs_3551_;
v___y_3476_ = v_sTerms_3555_;
v___y_3477_ = v___x_3562_;
v___y_3478_ = v_congr_3543_;
v___y_3479_ = v___y_3498_;
v___y_3480_ = v_mt_3554_;
v___y_3481_ = v___y_3501_;
v___y_3482_ = v_idx_3552_;
v___y_3483_ = v_funCC_3556_;
v___y_3484_ = v_root_3542_;
v___y_3485_ = v_flipped_3546_;
v___y_3486_ = v___y_3494_;
v___y_3487_ = v_target_x3f_3544_;
v___y_3488_ = v___y_3506_;
v___y_3489_ = v_interpreted_3548_;
v___y_3490_ = v___y_3503_;
v___y_3491_ = v___y_3513_;
v___y_3492_ = v_hasLambdas_3550_;
goto v___jp_3456_;
}
}
else
{
lean_dec(v___x_3517_);
lean_dec_ref(v___y_3505_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_lhs_3322_);
return v___x_3559_;
}
}
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec(v___x_3517_);
lean_dec_ref(v___y_3505_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_lhs_3322_);
v_a_3566_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3519_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3519_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
else
{
lean_dec_ref(v___y_3505_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_lhs_3322_);
return v___x_3516_;
}
}
v___jp_3578_:
{
lean_object* v_self_3594_; lean_object* v_next_3595_; lean_object* v_size_3596_; uint8_t v_hasLambdas_3597_; uint8_t v_heqProofs_3598_; lean_object* v___x_3599_; 
v_self_3594_ = lean_ctor_get(v_lhsRoot_3326_, 0);
v_next_3595_ = lean_ctor_get(v_lhsRoot_3326_, 1);
v_size_3596_ = lean_ctor_get(v_lhsRoot_3326_, 6);
v_hasLambdas_3597_ = lean_ctor_get_uint8(v_lhsRoot_3326_, sizeof(void*)*11 + 3);
v_heqProofs_3598_ = lean_ctor_get_uint8(v_lhsRoot_3326_, sizeof(void*)*11 + 4);
v___x_3599_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3594_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v_root_3601_; lean_object* v___x_3602_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref(v___x_3599_);
v_root_3601_ = lean_ctor_get(v_rhsNode_3325_, 2);
lean_inc_ref_n(v_root_3601_, 2);
lean_dec_ref(v_rhsNode_3325_);
lean_inc_ref(v_lhs_3322_);
v___x_3602_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3322_, v_root_3601_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_options_3603_; uint8_t v_hasTrace_3604_; 
lean_dec_ref(v___x_3602_);
v_options_3603_ = lean_ctor_get(v___y_3592_, 2);
v_hasTrace_3604_ = lean_ctor_get_uint8(v_options_3603_, sizeof(void*)*1);
if (v_hasTrace_3604_ == 0)
{
lean_inc(v_size_3596_);
lean_inc_ref(v_self_3594_);
lean_inc_ref(v_next_3595_);
v___y_3494_ = v_heqProofs_3598_;
v___y_3495_ = v___y_3579_;
v___y_3496_ = v_next_3595_;
v___y_3497_ = v_a_3600_;
v___y_3498_ = v_self_3594_;
v___y_3499_ = v_fns_u2082_3583_;
v___y_3500_ = v_size_3596_;
v___y_3501_ = v_root_3601_;
v___y_3502_ = v___y_3580_;
v___y_3503_ = v___y_3581_;
v___y_3504_ = v_hasLambdas_3597_;
v___y_3505_ = v___y_3582_;
v___y_3506_ = v___y_3584_;
v___y_3507_ = v___y_3585_;
v___y_3508_ = v___y_3586_;
v___y_3509_ = v___y_3587_;
v___y_3510_ = v___y_3588_;
v___y_3511_ = v___y_3589_;
v___y_3512_ = v___y_3590_;
v___y_3513_ = v___y_3591_;
v___y_3514_ = v___y_3592_;
v___y_3515_ = v___y_3593_;
goto v___jp_3493_;
}
else
{
lean_object* v_inheritedTraceOptions_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v_inheritedTraceOptions_3605_ = lean_ctor_get(v___y_3592_, 13);
v___x_3606_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3607_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3605_, v_options_3603_, v___x_3606_);
if (v___x_3607_ == 0)
{
lean_inc(v_size_3596_);
lean_inc_ref(v_self_3594_);
lean_inc_ref(v_next_3595_);
v___y_3494_ = v_heqProofs_3598_;
v___y_3495_ = v___y_3579_;
v___y_3496_ = v_next_3595_;
v___y_3497_ = v_a_3600_;
v___y_3498_ = v_self_3594_;
v___y_3499_ = v_fns_u2082_3583_;
v___y_3500_ = v_size_3596_;
v___y_3501_ = v_root_3601_;
v___y_3502_ = v___y_3580_;
v___y_3503_ = v___y_3581_;
v___y_3504_ = v_hasLambdas_3597_;
v___y_3505_ = v___y_3582_;
v___y_3506_ = v___y_3584_;
v___y_3507_ = v___y_3585_;
v___y_3508_ = v___y_3586_;
v___y_3509_ = v___y_3587_;
v___y_3510_ = v___y_3588_;
v___y_3511_ = v___y_3589_;
v___y_3512_ = v___y_3590_;
v___y_3513_ = v___y_3591_;
v___y_3514_ = v___y_3592_;
v___y_3515_ = v___y_3593_;
goto v___jp_3493_;
}
else
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Lean_Meta_Grind_updateLastTag(v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v___x_3609_; 
lean_dec_ref(v___x_3608_);
lean_inc_ref(v_lhs_3322_);
v___x_3609_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3322_, v___y_3584_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3611_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref(v___x_3609_);
lean_inc_ref(v_root_3601_);
v___x_3611_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3601_, v___y_3584_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref(v___x_3611_);
v___x_3613_ = lean_st_ref_get(v___y_3584_);
lean_inc_ref(v_lhs_3322_);
v___x_3614_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3613_, v_lhs_3322_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___x_3613_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3616_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref(v___x_3614_);
v___x_3616_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3615_, v___y_3584_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref(v___x_3616_);
v___x_3618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v_a_3610_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v_a_3612_);
v___x_3621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
lean_ctor_set(v___x_3623_, 1, v_a_3617_);
v___x_3624_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3577_, v___x_3623_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_dec_ref(v___x_3624_);
lean_inc(v_size_3596_);
lean_inc_ref(v_self_3594_);
lean_inc_ref(v_next_3595_);
v___y_3494_ = v_heqProofs_3598_;
v___y_3495_ = v___y_3579_;
v___y_3496_ = v_next_3595_;
v___y_3497_ = v_a_3600_;
v___y_3498_ = v_self_3594_;
v___y_3499_ = v_fns_u2082_3583_;
v___y_3500_ = v_size_3596_;
v___y_3501_ = v_root_3601_;
v___y_3502_ = v___y_3580_;
v___y_3503_ = v___y_3581_;
v___y_3504_ = v_hasLambdas_3597_;
v___y_3505_ = v___y_3582_;
v___y_3506_ = v___y_3584_;
v___y_3507_ = v___y_3585_;
v___y_3508_ = v___y_3586_;
v___y_3509_ = v___y_3587_;
v___y_3510_ = v___y_3588_;
v___y_3511_ = v___y_3589_;
v___y_3512_ = v___y_3590_;
v___y_3513_ = v___y_3591_;
v___y_3514_ = v___y_3592_;
v___y_3515_ = v___y_3593_;
goto v___jp_3493_;
}
else
{
lean_dec_ref(v_root_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_fns_u2082_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_lhs_3322_);
return v___x_3624_;
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v_a_3612_);
lean_dec(v_a_3610_);
lean_dec_ref(v_root_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_fns_u2082_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_lhs_3322_);
v_a_3625_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3616_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3616_);
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
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v_a_3612_);
lean_dec(v_a_3610_);
lean_dec_ref(v_root_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_fns_u2082_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_lhs_3322_);
v_a_3633_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3614_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3614_);
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
lean_dec(v_a_3610_);
lean_dec_ref(v_root_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_fns_u2082_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_lhs_3322_);
v_a_3641_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3611_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3611_);
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
lean_dec_ref(v_root_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_fns_u2082_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_lhs_3322_);
v_a_3649_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3609_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3609_);
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
lean_dec_ref(v_root_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_fns_u2082_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_lhs_3322_);
return v___x_3608_;
}
}
}
}
else
{
lean_dec_ref(v_root_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_fns_u2082_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_lhs_3322_);
return v___x_3602_;
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_dec_ref(v_fns_u2082_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhs_3322_);
v_a_3657_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3599_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3599_);
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
v___jp_3665_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v___x_3680_ = lean_array_get_size(v___y_3666_);
v___x_3681_ = lean_unsigned_to_nat(0u);
v___x_3682_ = lean_nat_dec_eq(v___x_3680_, v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v_self_3683_; lean_object* v___x_3684_; 
v_self_3683_ = lean_ctor_get(v_lhsRoot_3326_, 0);
lean_inc_ref(v_self_3683_);
v___x_3684_ = l_Lean_Meta_Grind_getFnRoots(v_self_3683_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref(v___x_3684_);
v___y_3579_ = v___y_3666_;
v___y_3580_ = v___y_3667_;
v___y_3581_ = v___y_3668_;
v___y_3582_ = v_fns_u2081_3669_;
v_fns_u2082_3583_ = v_a_3685_;
v___y_3584_ = v___y_3670_;
v___y_3585_ = v___y_3671_;
v___y_3586_ = v___y_3672_;
v___y_3587_ = v___y_3673_;
v___y_3588_ = v___y_3674_;
v___y_3589_ = v___y_3675_;
v___y_3590_ = v___y_3676_;
v___y_3591_ = v___y_3677_;
v___y_3592_ = v___y_3678_;
v___y_3593_ = v___y_3679_;
goto v___jp_3578_;
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec_ref(v_fns_u2081_3669_);
lean_dec_ref(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhs_3322_);
v_a_3686_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3684_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3684_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v___x_3694_; 
v___x_3694_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3579_ = v___y_3666_;
v___y_3580_ = v___y_3667_;
v___y_3581_ = v___y_3668_;
v___y_3582_ = v_fns_u2081_3669_;
v_fns_u2082_3583_ = v___x_3694_;
v___y_3584_ = v___y_3670_;
v___y_3585_ = v___y_3671_;
v___y_3586_ = v___y_3672_;
v___y_3587_ = v___y_3673_;
v___y_3588_ = v___y_3674_;
v___y_3589_ = v___y_3675_;
v___y_3590_ = v___y_3676_;
v___y_3591_ = v___y_3677_;
v___y_3592_ = v___y_3678_;
v___y_3593_ = v___y_3679_;
goto v___jp_3578_;
}
}
v___jp_3695_:
{
lean_object* v___x_3706_; 
lean_inc_ref(v_lhs_3322_);
v___x_3706_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3322_, v___y_3696_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3773_; 
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3773_ == 0)
{
lean_object* v_unused_3774_; 
v_unused_3774_ = lean_ctor_get(v___x_3706_, 0);
lean_dec(v_unused_3774_);
v___x_3708_ = v___x_3706_;
v_isShared_3709_ = v_isSharedCheck_3773_;
goto v_resetjp_3707_;
}
else
{
lean_dec(v___x_3706_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3773_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v_self_3710_; lean_object* v_next_3711_; lean_object* v_root_3712_; lean_object* v_congr_3713_; lean_object* v_size_3714_; uint8_t v_interpreted_3715_; uint8_t v_ctor_3716_; uint8_t v_hasLambdas_3717_; uint8_t v_heqProofs_3718_; lean_object* v_idx_3719_; lean_object* v_generation_3720_; lean_object* v_mt_3721_; lean_object* v_sTerms_3722_; uint8_t v_funCC_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3770_; 
v_self_3710_ = lean_ctor_get(v_lhsNode_3324_, 0);
v_next_3711_ = lean_ctor_get(v_lhsNode_3324_, 1);
v_root_3712_ = lean_ctor_get(v_lhsNode_3324_, 2);
v_congr_3713_ = lean_ctor_get(v_lhsNode_3324_, 3);
v_size_3714_ = lean_ctor_get(v_lhsNode_3324_, 6);
v_interpreted_3715_ = lean_ctor_get_uint8(v_lhsNode_3324_, sizeof(void*)*11 + 1);
v_ctor_3716_ = lean_ctor_get_uint8(v_lhsNode_3324_, sizeof(void*)*11 + 2);
v_hasLambdas_3717_ = lean_ctor_get_uint8(v_lhsNode_3324_, sizeof(void*)*11 + 3);
v_heqProofs_3718_ = lean_ctor_get_uint8(v_lhsNode_3324_, sizeof(void*)*11 + 4);
v_idx_3719_ = lean_ctor_get(v_lhsNode_3324_, 7);
v_generation_3720_ = lean_ctor_get(v_lhsNode_3324_, 8);
v_mt_3721_ = lean_ctor_get(v_lhsNode_3324_, 9);
v_sTerms_3722_ = lean_ctor_get(v_lhsNode_3324_, 10);
v_funCC_3723_ = lean_ctor_get_uint8(v_lhsNode_3324_, sizeof(void*)*11 + 5);
v_isSharedCheck_3770_ = !lean_is_exclusive(v_lhsNode_3324_);
if (v_isSharedCheck_3770_ == 0)
{
lean_object* v_unused_3771_; lean_object* v_unused_3772_; 
v_unused_3771_ = lean_ctor_get(v_lhsNode_3324_, 5);
lean_dec(v_unused_3771_);
v_unused_3772_ = lean_ctor_get(v_lhsNode_3324_, 4);
lean_dec(v_unused_3772_);
v___x_3725_ = v_lhsNode_3324_;
v_isShared_3726_ = v_isSharedCheck_3770_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_sTerms_3722_);
lean_inc(v_mt_3721_);
lean_inc(v_generation_3720_);
lean_inc(v_idx_3719_);
lean_inc(v_size_3714_);
lean_inc(v_congr_3713_);
lean_inc(v_root_3712_);
lean_inc(v_next_3711_);
lean_inc(v_self_3710_);
lean_dec(v_lhsNode_3324_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3770_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set_tag(v___x_3708_, 1);
lean_ctor_set(v___x_3708_, 0, v_rhs_3323_);
v___x_3728_ = v___x_3708_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_rhs_3323_);
v___x_3728_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_proof_3320_);
lean_inc_ref(v_root_3712_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 5, v___x_3729_);
lean_ctor_set(v___x_3725_, 4, v___x_3728_);
v___x_3731_ = v___x_3725_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_self_3710_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v_next_3711_);
lean_ctor_set(v_reuseFailAlloc_3768_, 2, v_root_3712_);
lean_ctor_set(v_reuseFailAlloc_3768_, 3, v_congr_3713_);
lean_ctor_set(v_reuseFailAlloc_3768_, 4, v___x_3728_);
lean_ctor_set(v_reuseFailAlloc_3768_, 5, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3768_, 6, v_size_3714_);
lean_ctor_set(v_reuseFailAlloc_3768_, 7, v_idx_3719_);
lean_ctor_set(v_reuseFailAlloc_3768_, 8, v_generation_3720_);
lean_ctor_set(v_reuseFailAlloc_3768_, 9, v_mt_3721_);
lean_ctor_set(v_reuseFailAlloc_3768_, 10, v_sTerms_3722_);
lean_ctor_set_uint8(v_reuseFailAlloc_3768_, sizeof(void*)*11 + 1, v_interpreted_3715_);
lean_ctor_set_uint8(v_reuseFailAlloc_3768_, sizeof(void*)*11 + 2, v_ctor_3716_);
lean_ctor_set_uint8(v_reuseFailAlloc_3768_, sizeof(void*)*11 + 3, v_hasLambdas_3717_);
lean_ctor_set_uint8(v_reuseFailAlloc_3768_, sizeof(void*)*11 + 4, v_heqProofs_3718_);
lean_ctor_set_uint8(v_reuseFailAlloc_3768_, sizeof(void*)*11 + 5, v_funCC_3723_);
v___x_3731_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; 
lean_ctor_set_uint8(v___x_3731_, sizeof(void*)*11, v_flipped_3328_);
lean_inc_ref(v_lhs_3322_);
v___x_3732_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3322_, v___x_3731_, v___y_3696_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v___x_3733_; 
lean_dec_ref(v___x_3732_);
v___x_3733_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3326_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref(v___x_3733_);
v___x_3735_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3327_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref(v___x_3735_);
v___x_3737_ = lean_array_get_size(v_a_3734_);
v___x_3738_ = lean_unsigned_to_nat(0u);
v___x_3739_ = lean_nat_dec_eq(v___x_3737_, v___x_3738_);
if (v___x_3739_ == 0)
{
lean_object* v_self_3740_; lean_object* v___x_3741_; 
v_self_3740_ = lean_ctor_get(v_rhsRoot_3327_, 0);
lean_inc_ref(v_self_3740_);
v___x_3741_ = l_Lean_Meta_Grind_getFnRoots(v_self_3740_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_a_3742_);
lean_dec_ref(v___x_3741_);
v___y_3666_ = v_a_3736_;
v___y_3667_ = v_root_3712_;
v___y_3668_ = v_a_3734_;
v_fns_u2081_3669_ = v_a_3742_;
v___y_3670_ = v___y_3696_;
v___y_3671_ = v___y_3697_;
v___y_3672_ = v___y_3698_;
v___y_3673_ = v___y_3699_;
v___y_3674_ = v___y_3700_;
v___y_3675_ = v___y_3701_;
v___y_3676_ = v___y_3702_;
v___y_3677_ = v___y_3703_;
v___y_3678_ = v___y_3704_;
v___y_3679_ = v___y_3705_;
goto v___jp_3665_;
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec(v_a_3736_);
lean_dec(v_a_3734_);
lean_dec_ref(v_root_3712_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhs_3322_);
v_a_3743_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3741_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3741_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_object* v___x_3751_; 
v___x_3751_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3666_ = v_a_3736_;
v___y_3667_ = v_root_3712_;
v___y_3668_ = v_a_3734_;
v_fns_u2081_3669_ = v___x_3751_;
v___y_3670_ = v___y_3696_;
v___y_3671_ = v___y_3697_;
v___y_3672_ = v___y_3698_;
v___y_3673_ = v___y_3699_;
v___y_3674_ = v___y_3700_;
v___y_3675_ = v___y_3701_;
v___y_3676_ = v___y_3702_;
v___y_3677_ = v___y_3703_;
v___y_3678_ = v___y_3704_;
v___y_3679_ = v___y_3705_;
goto v___jp_3665_;
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec(v_a_3734_);
lean_dec_ref(v_root_3712_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhs_3322_);
v_a_3752_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3735_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3735_);
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
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_dec_ref(v_root_3712_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhs_3322_);
v_a_3760_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3733_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3733_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_dec_ref(v_root_3712_);
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhs_3322_);
return v___x_3732_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3327_);
lean_dec_ref(v_lhsRoot_3326_);
lean_dec_ref(v_rhsNode_3325_);
lean_dec_ref(v_lhsNode_3324_);
lean_dec_ref(v_rhs_3323_);
lean_dec_ref(v_lhs_3322_);
lean_dec_ref(v_proof_3320_);
return v___x_3706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3804_ = _args[0];
lean_object* v_isHEq_3805_ = _args[1];
lean_object* v_lhs_3806_ = _args[2];
lean_object* v_rhs_3807_ = _args[3];
lean_object* v_lhsNode_3808_ = _args[4];
lean_object* v_rhsNode_3809_ = _args[5];
lean_object* v_lhsRoot_3810_ = _args[6];
lean_object* v_rhsRoot_3811_ = _args[7];
lean_object* v_flipped_3812_ = _args[8];
lean_object* v_a_3813_ = _args[9];
lean_object* v_a_3814_ = _args[10];
lean_object* v_a_3815_ = _args[11];
lean_object* v_a_3816_ = _args[12];
lean_object* v_a_3817_ = _args[13];
lean_object* v_a_3818_ = _args[14];
lean_object* v_a_3819_ = _args[15];
lean_object* v_a_3820_ = _args[16];
lean_object* v_a_3821_ = _args[17];
lean_object* v_a_3822_ = _args[18];
lean_object* v_a_3823_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3824_; uint8_t v_flipped_boxed_3825_; lean_object* v_res_3826_; 
v_isHEq_boxed_3824_ = lean_unbox(v_isHEq_3805_);
v_flipped_boxed_3825_ = lean_unbox(v_flipped_3812_);
v_res_3826_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3804_, v_isHEq_boxed_3824_, v_lhs_3806_, v_rhs_3807_, v_lhsNode_3808_, v_rhsNode_3809_, v_lhsRoot_3810_, v_rhsRoot_3811_, v_flipped_boxed_3825_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_);
lean_dec(v_a_3822_);
lean_dec_ref(v_a_3821_);
lean_dec(v_a_3820_);
lean_dec_ref(v_a_3819_);
lean_dec(v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_a_3816_);
lean_dec_ref(v_a_3815_);
lean_dec(v_a_3814_);
lean_dec(v_a_3813_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3827_, lean_object* v_as_x27_3828_, lean_object* v_b_3829_, lean_object* v_a_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3828_, v_b_3829_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3843_, lean_object* v_as_x27_3844_, lean_object* v_b_3845_, lean_object* v_a_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3843_, v_as_x27_3844_, v_b_3845_, v_a_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec(v_as_x27_3844_);
lean_dec(v_as_3843_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3859_, lean_object* v_as_x27_3860_, lean_object* v_b_3861_, lean_object* v_a_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3860_, v_b_3861_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3875_, lean_object* v_as_x27_3876_, lean_object* v_b_3877_, lean_object* v_a_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3875_, v_as_x27_3876_, v_b_3877_, v_a_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec(v_as_x27_3876_);
lean_dec(v_as_3875_);
return v_res_3890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_3893_ = l_Lean_stringToMessageData(v___x_3892_);
return v___x_3893_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_3899_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3900_ = l_Lean_Name_append(v___x_3899_, v___x_3898_);
return v___x_3900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_3903_ = l_Lean_stringToMessageData(v___x_3902_);
return v___x_3903_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_3906_ = l_Lean_stringToMessageData(v___x_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_3907_, lean_object* v_rhs_3908_, lean_object* v_proof_3909_, uint8_t v_isHEq_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = lean_st_ref_get(v_a_3911_);
lean_inc_ref(v_lhs_3907_);
v___x_3926_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3925_, v_lhs_3907_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
lean_dec(v___x_3925_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref(v___x_3926_);
v___x_3928_ = lean_st_ref_get(v_a_3911_);
lean_inc_ref(v_rhs_3908_);
v___x_3929_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3928_, v_rhs_3908_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
lean_dec(v___x_3928_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v_root_3931_; lean_object* v_root_3932_; uint8_t v___x_3933_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3930_);
lean_dec_ref(v___x_3929_);
v_root_3931_ = lean_ctor_get(v_a_3927_, 2);
v_root_3932_ = lean_ctor_get(v_a_3930_, 2);
v___x_3933_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_3931_, v_root_3932_);
if (v___x_3933_ == 0)
{
lean_object* v_options_3934_; lean_object* v_inheritedTraceOptions_3935_; uint8_t v_hasTrace_3936_; uint8_t v___x_3937_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3974_; uint8_t v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; uint8_t v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; uint8_t v___y_4015_; lean_object* v___y_4020_; uint8_t v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4047_; uint8_t v___y_4048_; uint8_t v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4063_; uint8_t v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; uint8_t v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4079_; uint8_t v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; uint8_t v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4095_; uint8_t v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; uint8_t v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; uint8_t v___y_4109_; lean_object* v___y_4111_; lean_object* v_size_4112_; uint8_t v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v_size_4116_; uint8_t v_interpreted_4117_; uint8_t v_ctor_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; uint8_t v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4131_; uint8_t v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; uint8_t v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; uint8_t v___y_4145_; lean_object* v___y_4156_; uint8_t v_interpreted_4157_; lean_object* v___y_4158_; uint8_t v_valueInconsistency_4159_; uint8_t v_trueEqFalse_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4173_; lean_object* v___y_4174_; uint8_t v_valueInconsistency_4175_; uint8_t v_trueEqFalse_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; uint8_t v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; uint8_t v___y_4243_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; 
v_options_3934_ = lean_ctor_get(v_a_3919_, 2);
v_inheritedTraceOptions_3935_ = lean_ctor_get(v_a_3919_, 13);
v_hasTrace_3936_ = lean_ctor_get_uint8(v_options_3934_, sizeof(void*)*1);
v___x_3937_ = 1;
if (v_hasTrace_3936_ == 0)
{
v___y_4250_ = v_a_3911_;
v___y_4251_ = v_a_3912_;
v___y_4252_ = v_a_3913_;
v___y_4253_ = v_a_3914_;
v___y_4254_ = v_a_3915_;
v___y_4255_ = v_a_3916_;
v___y_4256_ = v_a_3917_;
v___y_4257_ = v_a_3918_;
v___y_4258_ = v_a_3919_;
v___y_4259_ = v_a_3920_;
goto v___jp_4249_;
}
else
{
lean_object* v___x_4285_; lean_object* v___y_4287_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4300_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3935_, v_options_3934_, v___x_4299_);
if (v___x_4300_ == 0)
{
v___y_4250_ = v_a_3911_;
v___y_4251_ = v_a_3912_;
v___y_4252_ = v_a_3913_;
v___y_4253_ = v_a_3914_;
v___y_4254_ = v_a_3915_;
v___y_4255_ = v_a_3916_;
v___y_4256_ = v_a_3917_;
v___y_4257_ = v_a_3918_;
v___y_4258_ = v_a_3919_;
v___y_4259_ = v_a_3920_;
goto v___jp_4249_;
}
else
{
lean_object* v___x_4301_; 
v___x_4301_ = l_Lean_Meta_Grind_updateLastTag(v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_dec_ref(v___x_4301_);
if (v_isHEq_3910_ == 0)
{
lean_object* v___x_4302_; 
lean_inc_ref(v_rhs_3908_);
lean_inc_ref(v_lhs_3907_);
v___x_4302_ = l_Lean_Meta_mkEq(v_lhs_3907_, v_rhs_3908_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
v___y_4287_ = v___x_4302_;
goto v___jp_4286_;
}
else
{
lean_object* v___x_4303_; 
lean_inc_ref(v_rhs_3908_);
lean_inc_ref(v_lhs_3907_);
v___x_4303_ = l_Lean_Meta_mkHEq(v_lhs_3907_, v_rhs_3908_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
v___y_4287_ = v___x_4303_;
goto v___jp_4286_;
}
}
else
{
lean_dec(v_a_3930_);
lean_dec(v_a_3927_);
lean_dec_ref(v_proof_3909_);
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
return v___x_4301_;
}
}
v___jp_4286_:
{
if (lean_obj_tag(v___y_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v_a_4288_ = lean_ctor_get(v___y_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref(v___y_4287_);
v___x_4289_ = l_Lean_MessageData_ofExpr(v_a_4288_);
v___x_4290_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4285_, v___x_4289_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_dec_ref(v___x_4290_);
v___y_4250_ = v_a_3911_;
v___y_4251_ = v_a_3912_;
v___y_4252_ = v_a_3913_;
v___y_4253_ = v_a_3914_;
v___y_4254_ = v_a_3915_;
v___y_4255_ = v_a_3916_;
v___y_4256_ = v_a_3917_;
v___y_4257_ = v_a_3918_;
v___y_4258_ = v_a_3919_;
v___y_4259_ = v_a_3920_;
goto v___jp_4249_;
}
else
{
lean_dec(v_a_3930_);
lean_dec(v_a_3927_);
lean_dec_ref(v_proof_3909_);
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
return v___x_4290_;
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
lean_dec(v_a_3930_);
lean_dec(v_a_3927_);
lean_dec_ref(v_proof_3909_);
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
v_a_4291_ = lean_ctor_get(v___y_4287_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___y_4287_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___y_4287_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___y_4287_);
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
}
v___jp_3938_:
{
lean_object* v_options_3949_; uint8_t v_hasTrace_3950_; 
v_options_3949_ = lean_ctor_get(v___y_3947_, 2);
v_hasTrace_3950_ = lean_ctor_get_uint8(v_options_3949_, sizeof(void*)*1);
if (v_hasTrace_3950_ == 0)
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_Meta_Grind_checkInvariants(v___x_3933_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
return v___x_3951_;
}
else
{
lean_object* v_inheritedTraceOptions_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v_inheritedTraceOptions_3952_ = lean_ctor_get(v___y_3947_, 13);
v___x_3953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3954_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3955_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3952_, v_options_3949_, v___x_3954_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_Meta_Grind_checkInvariants(v___x_3933_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
return v___x_3956_;
}
else
{
lean_object* v___x_3957_; 
v___x_3957_ = l_Lean_Meta_Grind_updateLastTag(v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
lean_dec_ref(v___x_3957_);
v___x_3958_ = lean_st_ref_get(v___y_3939_);
v___x_3959_ = l_Lean_Meta_Grind_Goal_ppState(v___x_3958_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
lean_dec(v___x_3958_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref(v___x_3959_);
v___x_3961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_3962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v_a_3960_);
v___x_3963_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_3953_, v___x_3962_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v___x_3964_; 
lean_dec_ref(v___x_3963_);
v___x_3964_ = l_Lean_Meta_Grind_checkInvariants(v___x_3933_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
return v___x_3964_;
}
else
{
return v___x_3963_;
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
v_a_3965_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3959_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3959_);
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
return v___x_3957_;
}
}
}
}
v___jp_3973_:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3977_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; uint8_t v___x_3989_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
lean_dec_ref(v___x_3987_);
v___x_3989_ = lean_unbox(v_a_3988_);
lean_dec(v_a_3988_);
if (v___x_3989_ == 0)
{
if (v___y_3975_ == 0)
{
lean_dec_ref(v___y_3976_);
lean_dec_ref(v___y_3974_);
v___y_3939_ = v___y_3977_;
v___y_3940_ = v___y_3978_;
v___y_3941_ = v___y_3979_;
v___y_3942_ = v___y_3980_;
v___y_3943_ = v___y_3981_;
v___y_3944_ = v___y_3982_;
v___y_3945_ = v___y_3983_;
v___y_3946_ = v___y_3984_;
v___y_3947_ = v___y_3985_;
v___y_3948_ = v___y_3986_;
goto v___jp_3938_;
}
else
{
lean_object* v_self_3990_; lean_object* v_self_3991_; lean_object* v___x_3992_; 
v_self_3990_ = lean_ctor_get(v___y_3974_, 0);
lean_inc_ref(v_self_3990_);
lean_dec_ref(v___y_3974_);
v_self_3991_ = lean_ctor_get(v___y_3976_, 0);
lean_inc_ref(v_self_3991_);
lean_dec_ref(v___y_3976_);
v___x_3992_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_3990_, v_self_3991_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_dec_ref(v___x_3992_);
v___y_3939_ = v___y_3977_;
v___y_3940_ = v___y_3978_;
v___y_3941_ = v___y_3979_;
v___y_3942_ = v___y_3980_;
v___y_3943_ = v___y_3981_;
v___y_3944_ = v___y_3982_;
v___y_3945_ = v___y_3983_;
v___y_3946_ = v___y_3984_;
v___y_3947_ = v___y_3985_;
v___y_3948_ = v___y_3986_;
goto v___jp_3938_;
}
else
{
return v___x_3992_;
}
}
}
else
{
lean_dec_ref(v___y_3976_);
lean_dec_ref(v___y_3974_);
v___y_3939_ = v___y_3977_;
v___y_3940_ = v___y_3978_;
v___y_3941_ = v___y_3979_;
v___y_3942_ = v___y_3980_;
v___y_3943_ = v___y_3981_;
v___y_3944_ = v___y_3982_;
v___y_3945_ = v___y_3983_;
v___y_3946_ = v___y_3984_;
v___y_3947_ = v___y_3985_;
v___y_3948_ = v___y_3986_;
goto v___jp_3938_;
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec_ref(v___y_3976_);
lean_dec_ref(v___y_3974_);
v_a_3993_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3987_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3987_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
v___jp_4001_:
{
if (v___y_4015_ == 0)
{
v___y_3974_ = v___y_4003_;
v___y_3975_ = v___y_4011_;
v___y_3976_ = v___y_4008_;
v___y_3977_ = v___y_4004_;
v___y_3978_ = v___y_4013_;
v___y_3979_ = v___y_4012_;
v___y_3980_ = v___y_4006_;
v___y_3981_ = v___y_4010_;
v___y_3982_ = v___y_4002_;
v___y_3983_ = v___y_4007_;
v___y_3984_ = v___y_4009_;
v___y_3985_ = v___y_4005_;
v___y_3986_ = v___y_4014_;
goto v___jp_3973_;
}
else
{
lean_object* v_self_4016_; lean_object* v_self_4017_; lean_object* v___x_4018_; 
v_self_4016_ = lean_ctor_get(v___y_4003_, 0);
v_self_4017_ = lean_ctor_get(v___y_4008_, 0);
lean_inc_ref(v_self_4017_);
lean_inc_ref(v_self_4016_);
v___x_4018_ = l_Lean_Meta_Grind_propagateCtor(v_self_4016_, v_self_4017_, v___y_4004_, v___y_4013_, v___y_4012_, v___y_4006_, v___y_4010_, v___y_4002_, v___y_4007_, v___y_4009_, v___y_4005_, v___y_4014_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_dec_ref(v___x_4018_);
v___y_3974_ = v___y_4003_;
v___y_3975_ = v___y_4011_;
v___y_3976_ = v___y_4008_;
v___y_3977_ = v___y_4004_;
v___y_3978_ = v___y_4013_;
v___y_3979_ = v___y_4012_;
v___y_3980_ = v___y_4006_;
v___y_3981_ = v___y_4010_;
v___y_3982_ = v___y_4002_;
v___y_3983_ = v___y_4007_;
v___y_3984_ = v___y_4009_;
v___y_3985_ = v___y_4005_;
v___y_3986_ = v___y_4014_;
goto v___jp_3973_;
}
else
{
lean_dec_ref(v___y_4008_);
lean_dec_ref(v___y_4003_);
return v___x_4018_;
}
}
}
v___jp_4019_:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4023_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; uint8_t v___x_4035_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref(v___x_4033_);
v___x_4035_ = lean_unbox(v_a_4034_);
lean_dec(v_a_4034_);
if (v___x_4035_ == 0)
{
uint8_t v_ctor_4036_; 
v_ctor_4036_ = lean_ctor_get_uint8(v___y_4020_, sizeof(void*)*11 + 2);
if (v_ctor_4036_ == 0)
{
v___y_4002_ = v___y_4028_;
v___y_4003_ = v___y_4020_;
v___y_4004_ = v___y_4023_;
v___y_4005_ = v___y_4031_;
v___y_4006_ = v___y_4026_;
v___y_4007_ = v___y_4029_;
v___y_4008_ = v___y_4022_;
v___y_4009_ = v___y_4030_;
v___y_4010_ = v___y_4027_;
v___y_4011_ = v___y_4021_;
v___y_4012_ = v___y_4025_;
v___y_4013_ = v___y_4024_;
v___y_4014_ = v___y_4032_;
v___y_4015_ = v___x_3933_;
goto v___jp_4001_;
}
else
{
uint8_t v_ctor_4037_; 
v_ctor_4037_ = lean_ctor_get_uint8(v___y_4022_, sizeof(void*)*11 + 2);
v___y_4002_ = v___y_4028_;
v___y_4003_ = v___y_4020_;
v___y_4004_ = v___y_4023_;
v___y_4005_ = v___y_4031_;
v___y_4006_ = v___y_4026_;
v___y_4007_ = v___y_4029_;
v___y_4008_ = v___y_4022_;
v___y_4009_ = v___y_4030_;
v___y_4010_ = v___y_4027_;
v___y_4011_ = v___y_4021_;
v___y_4012_ = v___y_4025_;
v___y_4013_ = v___y_4024_;
v___y_4014_ = v___y_4032_;
v___y_4015_ = v_ctor_4037_;
goto v___jp_4001_;
}
}
else
{
v___y_3974_ = v___y_4020_;
v___y_3975_ = v___y_4021_;
v___y_3976_ = v___y_4022_;
v___y_3977_ = v___y_4023_;
v___y_3978_ = v___y_4024_;
v___y_3979_ = v___y_4025_;
v___y_3980_ = v___y_4026_;
v___y_3981_ = v___y_4027_;
v___y_3982_ = v___y_4028_;
v___y_3983_ = v___y_4029_;
v___y_3984_ = v___y_4030_;
v___y_3985_ = v___y_4031_;
v___y_3986_ = v___y_4032_;
goto v___jp_3973_;
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec_ref(v___y_4022_);
lean_dec_ref(v___y_4020_);
v_a_4038_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4033_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4033_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
v___jp_4046_:
{
if (v___y_4049_ == 0)
{
v___y_4020_ = v___y_4047_;
v___y_4021_ = v___y_4048_;
v___y_4022_ = v___y_4050_;
v___y_4023_ = v___y_4051_;
v___y_4024_ = v___y_4052_;
v___y_4025_ = v___y_4053_;
v___y_4026_ = v___y_4054_;
v___y_4027_ = v___y_4055_;
v___y_4028_ = v___y_4056_;
v___y_4029_ = v___y_4057_;
v___y_4030_ = v___y_4058_;
v___y_4031_ = v___y_4059_;
v___y_4032_ = v___y_4060_;
goto v___jp_4019_;
}
else
{
lean_object* v___x_4061_; 
v___x_4061_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_dec_ref(v___x_4061_);
v___y_4020_ = v___y_4047_;
v___y_4021_ = v___y_4048_;
v___y_4022_ = v___y_4050_;
v___y_4023_ = v___y_4051_;
v___y_4024_ = v___y_4052_;
v___y_4025_ = v___y_4053_;
v___y_4026_ = v___y_4054_;
v___y_4027_ = v___y_4055_;
v___y_4028_ = v___y_4056_;
v___y_4029_ = v___y_4057_;
v___y_4030_ = v___y_4058_;
v___y_4031_ = v___y_4059_;
v___y_4032_ = v___y_4060_;
goto v___jp_4019_;
}
else
{
lean_dec_ref(v___y_4050_);
lean_dec_ref(v___y_4047_);
return v___x_4061_;
}
}
}
v___jp_4062_:
{
lean_object* v___x_4077_; 
lean_inc_ref(v___y_4063_);
lean_inc_ref(v___y_4066_);
v___x_4077_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3909_, v_isHEq_3910_, v_rhs_3908_, v_lhs_3907_, v_a_3930_, v_a_3927_, v___y_4066_, v___y_4063_, v___x_3937_, v___y_4075_, v___y_4076_, v___y_4072_, v___y_4070_, v___y_4071_, v___y_4065_, v___y_4067_, v___y_4068_, v___y_4074_, v___y_4073_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_dec_ref(v___x_4077_);
v___y_4047_ = v___y_4063_;
v___y_4048_ = v___y_4069_;
v___y_4049_ = v___y_4064_;
v___y_4050_ = v___y_4066_;
v___y_4051_ = v___y_4075_;
v___y_4052_ = v___y_4076_;
v___y_4053_ = v___y_4072_;
v___y_4054_ = v___y_4070_;
v___y_4055_ = v___y_4071_;
v___y_4056_ = v___y_4065_;
v___y_4057_ = v___y_4067_;
v___y_4058_ = v___y_4068_;
v___y_4059_ = v___y_4074_;
v___y_4060_ = v___y_4073_;
goto v___jp_4046_;
}
else
{
lean_dec_ref(v___y_4066_);
lean_dec_ref(v___y_4063_);
return v___x_4077_;
}
}
v___jp_4078_:
{
lean_object* v___x_4093_; 
lean_inc_ref(v___y_4082_);
lean_inc_ref(v___y_4079_);
v___x_4093_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3909_, v_isHEq_3910_, v_lhs_3907_, v_rhs_3908_, v_a_3927_, v_a_3930_, v___y_4079_, v___y_4082_, v___x_3933_, v___y_4091_, v___y_4092_, v___y_4088_, v___y_4086_, v___y_4087_, v___y_4081_, v___y_4083_, v___y_4084_, v___y_4090_, v___y_4089_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_dec_ref(v___x_4093_);
v___y_4047_ = v___y_4079_;
v___y_4048_ = v___y_4085_;
v___y_4049_ = v___y_4080_;
v___y_4050_ = v___y_4082_;
v___y_4051_ = v___y_4091_;
v___y_4052_ = v___y_4092_;
v___y_4053_ = v___y_4088_;
v___y_4054_ = v___y_4086_;
v___y_4055_ = v___y_4087_;
v___y_4056_ = v___y_4081_;
v___y_4057_ = v___y_4083_;
v___y_4058_ = v___y_4084_;
v___y_4059_ = v___y_4090_;
v___y_4060_ = v___y_4089_;
goto v___jp_4046_;
}
else
{
lean_dec_ref(v___y_4082_);
lean_dec_ref(v___y_4079_);
return v___x_4093_;
}
}
v___jp_4094_:
{
if (v___y_4109_ == 0)
{
v___y_4079_ = v___y_4095_;
v___y_4080_ = v___y_4096_;
v___y_4081_ = v___y_4097_;
v___y_4082_ = v___y_4098_;
v___y_4083_ = v___y_4099_;
v___y_4084_ = v___y_4100_;
v___y_4085_ = v___y_4101_;
v___y_4086_ = v___y_4102_;
v___y_4087_ = v___y_4103_;
v___y_4088_ = v___y_4104_;
v___y_4089_ = v___y_4105_;
v___y_4090_ = v___y_4106_;
v___y_4091_ = v___y_4107_;
v___y_4092_ = v___y_4108_;
goto v___jp_4078_;
}
else
{
v___y_4063_ = v___y_4095_;
v___y_4064_ = v___y_4096_;
v___y_4065_ = v___y_4097_;
v___y_4066_ = v___y_4098_;
v___y_4067_ = v___y_4099_;
v___y_4068_ = v___y_4100_;
v___y_4069_ = v___y_4101_;
v___y_4070_ = v___y_4102_;
v___y_4071_ = v___y_4103_;
v___y_4072_ = v___y_4104_;
v___y_4073_ = v___y_4105_;
v___y_4074_ = v___y_4106_;
v___y_4075_ = v___y_4107_;
v___y_4076_ = v___y_4108_;
goto v___jp_4062_;
}
}
v___jp_4110_:
{
uint8_t v___x_4129_; 
v___x_4129_ = lean_nat_dec_lt(v_size_4116_, v_size_4112_);
lean_dec(v_size_4112_);
lean_dec(v_size_4116_);
if (v___x_4129_ == 0)
{
v___y_4095_ = v___y_4111_;
v___y_4096_ = v___y_4113_;
v___y_4097_ = v___y_4114_;
v___y_4098_ = v___y_4115_;
v___y_4099_ = v___y_4119_;
v___y_4100_ = v___y_4120_;
v___y_4101_ = v___y_4121_;
v___y_4102_ = v___y_4122_;
v___y_4103_ = v___y_4123_;
v___y_4104_ = v___y_4124_;
v___y_4105_ = v___y_4125_;
v___y_4106_ = v___y_4126_;
v___y_4107_ = v___y_4127_;
v___y_4108_ = v___y_4128_;
v___y_4109_ = v___x_3933_;
goto v___jp_4094_;
}
else
{
if (v_interpreted_4117_ == 0)
{
if (v___x_4129_ == 0)
{
v___y_4095_ = v___y_4111_;
v___y_4096_ = v___y_4113_;
v___y_4097_ = v___y_4114_;
v___y_4098_ = v___y_4115_;
v___y_4099_ = v___y_4119_;
v___y_4100_ = v___y_4120_;
v___y_4101_ = v___y_4121_;
v___y_4102_ = v___y_4122_;
v___y_4103_ = v___y_4123_;
v___y_4104_ = v___y_4124_;
v___y_4105_ = v___y_4125_;
v___y_4106_ = v___y_4126_;
v___y_4107_ = v___y_4127_;
v___y_4108_ = v___y_4128_;
v___y_4109_ = v___x_3933_;
goto v___jp_4094_;
}
else
{
if (v_ctor_4118_ == 0)
{
v___y_4095_ = v___y_4111_;
v___y_4096_ = v___y_4113_;
v___y_4097_ = v___y_4114_;
v___y_4098_ = v___y_4115_;
v___y_4099_ = v___y_4119_;
v___y_4100_ = v___y_4120_;
v___y_4101_ = v___y_4121_;
v___y_4102_ = v___y_4122_;
v___y_4103_ = v___y_4123_;
v___y_4104_ = v___y_4124_;
v___y_4105_ = v___y_4125_;
v___y_4106_ = v___y_4126_;
v___y_4107_ = v___y_4127_;
v___y_4108_ = v___y_4128_;
v___y_4109_ = v___x_4129_;
goto v___jp_4094_;
}
else
{
v___y_4079_ = v___y_4111_;
v___y_4080_ = v___y_4113_;
v___y_4081_ = v___y_4114_;
v___y_4082_ = v___y_4115_;
v___y_4083_ = v___y_4119_;
v___y_4084_ = v___y_4120_;
v___y_4085_ = v___y_4121_;
v___y_4086_ = v___y_4122_;
v___y_4087_ = v___y_4123_;
v___y_4088_ = v___y_4124_;
v___y_4089_ = v___y_4125_;
v___y_4090_ = v___y_4126_;
v___y_4091_ = v___y_4127_;
v___y_4092_ = v___y_4128_;
goto v___jp_4078_;
}
}
}
else
{
v___y_4095_ = v___y_4111_;
v___y_4096_ = v___y_4113_;
v___y_4097_ = v___y_4114_;
v___y_4098_ = v___y_4115_;
v___y_4099_ = v___y_4119_;
v___y_4100_ = v___y_4120_;
v___y_4101_ = v___y_4121_;
v___y_4102_ = v___y_4122_;
v___y_4103_ = v___y_4123_;
v___y_4104_ = v___y_4124_;
v___y_4105_ = v___y_4125_;
v___y_4106_ = v___y_4126_;
v___y_4107_ = v___y_4127_;
v___y_4108_ = v___y_4128_;
v___y_4109_ = v___x_3933_;
goto v___jp_4094_;
}
}
}
v___jp_4130_:
{
if (v___y_4145_ == 0)
{
uint8_t v_ctor_4146_; 
v_ctor_4146_ = lean_ctor_get_uint8(v___y_4131_, sizeof(void*)*11 + 2);
if (v_ctor_4146_ == 0)
{
if (v___x_3933_ == 0)
{
lean_object* v_size_4147_; lean_object* v_size_4148_; uint8_t v_interpreted_4149_; uint8_t v_ctor_4150_; 
v_size_4147_ = lean_ctor_get(v___y_4131_, 6);
lean_inc(v_size_4147_);
v_size_4148_ = lean_ctor_get(v___y_4134_, 6);
lean_inc(v_size_4148_);
v_interpreted_4149_ = lean_ctor_get_uint8(v___y_4134_, sizeof(void*)*11 + 1);
v_ctor_4150_ = lean_ctor_get_uint8(v___y_4134_, sizeof(void*)*11 + 2);
v___y_4111_ = v___y_4131_;
v_size_4112_ = v_size_4147_;
v___y_4113_ = v___y_4132_;
v___y_4114_ = v___y_4133_;
v___y_4115_ = v___y_4134_;
v_size_4116_ = v_size_4148_;
v_interpreted_4117_ = v_interpreted_4149_;
v_ctor_4118_ = v_ctor_4150_;
v___y_4119_ = v___y_4135_;
v___y_4120_ = v___y_4136_;
v___y_4121_ = v___y_4137_;
v___y_4122_ = v___y_4138_;
v___y_4123_ = v___y_4139_;
v___y_4124_ = v___y_4140_;
v___y_4125_ = v___y_4141_;
v___y_4126_ = v___y_4142_;
v___y_4127_ = v___y_4143_;
v___y_4128_ = v___y_4144_;
goto v___jp_4110_;
}
else
{
v___y_4063_ = v___y_4131_;
v___y_4064_ = v___y_4132_;
v___y_4065_ = v___y_4133_;
v___y_4066_ = v___y_4134_;
v___y_4067_ = v___y_4135_;
v___y_4068_ = v___y_4136_;
v___y_4069_ = v___y_4137_;
v___y_4070_ = v___y_4138_;
v___y_4071_ = v___y_4139_;
v___y_4072_ = v___y_4140_;
v___y_4073_ = v___y_4141_;
v___y_4074_ = v___y_4142_;
v___y_4075_ = v___y_4143_;
v___y_4076_ = v___y_4144_;
goto v___jp_4062_;
}
}
else
{
uint8_t v_ctor_4151_; 
v_ctor_4151_ = lean_ctor_get_uint8(v___y_4134_, sizeof(void*)*11 + 2);
if (v_ctor_4151_ == 0)
{
v___y_4063_ = v___y_4131_;
v___y_4064_ = v___y_4132_;
v___y_4065_ = v___y_4133_;
v___y_4066_ = v___y_4134_;
v___y_4067_ = v___y_4135_;
v___y_4068_ = v___y_4136_;
v___y_4069_ = v___y_4137_;
v___y_4070_ = v___y_4138_;
v___y_4071_ = v___y_4139_;
v___y_4072_ = v___y_4140_;
v___y_4073_ = v___y_4141_;
v___y_4074_ = v___y_4142_;
v___y_4075_ = v___y_4143_;
v___y_4076_ = v___y_4144_;
goto v___jp_4062_;
}
else
{
lean_object* v_size_4152_; lean_object* v_size_4153_; uint8_t v_interpreted_4154_; 
v_size_4152_ = lean_ctor_get(v___y_4131_, 6);
lean_inc(v_size_4152_);
v_size_4153_ = lean_ctor_get(v___y_4134_, 6);
lean_inc(v_size_4153_);
v_interpreted_4154_ = lean_ctor_get_uint8(v___y_4134_, sizeof(void*)*11 + 1);
v___y_4111_ = v___y_4131_;
v_size_4112_ = v_size_4152_;
v___y_4113_ = v___y_4132_;
v___y_4114_ = v___y_4133_;
v___y_4115_ = v___y_4134_;
v_size_4116_ = v_size_4153_;
v_interpreted_4117_ = v_interpreted_4154_;
v_ctor_4118_ = v_ctor_4151_;
v___y_4119_ = v___y_4135_;
v___y_4120_ = v___y_4136_;
v___y_4121_ = v___y_4137_;
v___y_4122_ = v___y_4138_;
v___y_4123_ = v___y_4139_;
v___y_4124_ = v___y_4140_;
v___y_4125_ = v___y_4141_;
v___y_4126_ = v___y_4142_;
v___y_4127_ = v___y_4143_;
v___y_4128_ = v___y_4144_;
goto v___jp_4110_;
}
}
}
else
{
v___y_4063_ = v___y_4131_;
v___y_4064_ = v___y_4132_;
v___y_4065_ = v___y_4133_;
v___y_4066_ = v___y_4134_;
v___y_4067_ = v___y_4135_;
v___y_4068_ = v___y_4136_;
v___y_4069_ = v___y_4137_;
v___y_4070_ = v___y_4138_;
v___y_4071_ = v___y_4139_;
v___y_4072_ = v___y_4140_;
v___y_4073_ = v___y_4141_;
v___y_4074_ = v___y_4142_;
v___y_4075_ = v___y_4143_;
v___y_4076_ = v___y_4144_;
goto v___jp_4062_;
}
}
v___jp_4155_:
{
if (v_interpreted_4157_ == 0)
{
v___y_4131_ = v___y_4156_;
v___y_4132_ = v_trueEqFalse_4160_;
v___y_4133_ = v___y_4166_;
v___y_4134_ = v___y_4158_;
v___y_4135_ = v___y_4167_;
v___y_4136_ = v___y_4168_;
v___y_4137_ = v_valueInconsistency_4159_;
v___y_4138_ = v___y_4164_;
v___y_4139_ = v___y_4165_;
v___y_4140_ = v___y_4163_;
v___y_4141_ = v___y_4170_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4161_;
v___y_4144_ = v___y_4162_;
v___y_4145_ = v___x_3933_;
goto v___jp_4130_;
}
else
{
uint8_t v_interpreted_4171_; 
v_interpreted_4171_ = lean_ctor_get_uint8(v___y_4158_, sizeof(void*)*11 + 1);
if (v_interpreted_4171_ == 0)
{
v___y_4063_ = v___y_4156_;
v___y_4064_ = v_trueEqFalse_4160_;
v___y_4065_ = v___y_4166_;
v___y_4066_ = v___y_4158_;
v___y_4067_ = v___y_4167_;
v___y_4068_ = v___y_4168_;
v___y_4069_ = v_valueInconsistency_4159_;
v___y_4070_ = v___y_4164_;
v___y_4071_ = v___y_4165_;
v___y_4072_ = v___y_4163_;
v___y_4073_ = v___y_4170_;
v___y_4074_ = v___y_4169_;
v___y_4075_ = v___y_4161_;
v___y_4076_ = v___y_4162_;
goto v___jp_4062_;
}
else
{
v___y_4131_ = v___y_4156_;
v___y_4132_ = v_trueEqFalse_4160_;
v___y_4133_ = v___y_4166_;
v___y_4134_ = v___y_4158_;
v___y_4135_ = v___y_4167_;
v___y_4136_ = v___y_4168_;
v___y_4137_ = v_valueInconsistency_4159_;
v___y_4138_ = v___y_4164_;
v___y_4139_ = v___y_4165_;
v___y_4140_ = v___y_4163_;
v___y_4141_ = v___y_4170_;
v___y_4142_ = v___y_4169_;
v___y_4143_ = v___y_4161_;
v___y_4144_ = v___y_4162_;
v___y_4145_ = v___x_3933_;
goto v___jp_4130_;
}
}
}
v___jp_4172_:
{
uint8_t v_interpreted_4187_; 
v_interpreted_4187_ = lean_ctor_get_uint8(v___y_4173_, sizeof(void*)*11 + 1);
v___y_4156_ = v___y_4173_;
v_interpreted_4157_ = v_interpreted_4187_;
v___y_4158_ = v___y_4174_;
v_valueInconsistency_4159_ = v_valueInconsistency_4175_;
v_trueEqFalse_4160_ = v_trueEqFalse_4176_;
v___y_4161_ = v___y_4177_;
v___y_4162_ = v___y_4178_;
v___y_4163_ = v___y_4179_;
v___y_4164_ = v___y_4180_;
v___y_4165_ = v___y_4181_;
v___y_4166_ = v___y_4182_;
v___y_4167_ = v___y_4183_;
v___y_4168_ = v___y_4184_;
v___y_4169_ = v___y_4185_;
v___y_4170_ = v___y_4186_;
goto v___jp_4155_;
}
v___jp_4188_:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4193_, v___y_4192_, v___y_4199_, v___y_4191_, v___y_4197_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_dec_ref(v___x_4201_);
v___y_4173_ = v___y_4189_;
v___y_4174_ = v___y_4194_;
v_valueInconsistency_4175_ = v___x_3933_;
v_trueEqFalse_4176_ = v___x_3937_;
v___y_4177_ = v___y_4193_;
v___y_4178_ = v___y_4195_;
v___y_4179_ = v___y_4200_;
v___y_4180_ = v___y_4196_;
v___y_4181_ = v___y_4190_;
v___y_4182_ = v___y_4198_;
v___y_4183_ = v___y_4192_;
v___y_4184_ = v___y_4199_;
v___y_4185_ = v___y_4191_;
v___y_4186_ = v___y_4197_;
goto v___jp_4172_;
}
else
{
lean_dec_ref(v___y_4194_);
lean_dec_ref(v___y_4189_);
lean_dec(v_a_3930_);
lean_dec(v_a_3927_);
lean_dec_ref(v_proof_3909_);
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
return v___x_4201_;
}
}
v___jp_4202_:
{
if (v___y_4206_ == 0)
{
lean_object* v_self_4216_; uint8_t v_interpreted_4217_; lean_object* v_self_4218_; lean_object* v___x_4219_; 
v_self_4216_ = lean_ctor_get(v___y_4203_, 0);
v_interpreted_4217_ = lean_ctor_get_uint8(v___y_4203_, sizeof(void*)*11 + 1);
v_self_4218_ = lean_ctor_get(v___y_4208_, 0);
lean_inc_ref(v_self_4218_);
lean_inc_ref(v_self_4216_);
v___x_4219_ = l_Lean_Meta_Grind_hasSameType(v_self_4216_, v_self_4218_, v___y_4207_, v___y_4214_, v___y_4205_, v___y_4212_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; uint8_t v___x_4221_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref(v___x_4219_);
v___x_4221_ = lean_unbox(v_a_4220_);
lean_dec(v_a_4220_);
if (v___x_4221_ == 0)
{
v___y_4156_ = v___y_4203_;
v_interpreted_4157_ = v_interpreted_4217_;
v___y_4158_ = v___y_4208_;
v_valueInconsistency_4159_ = v___x_3933_;
v_trueEqFalse_4160_ = v___x_3933_;
v___y_4161_ = v___y_4209_;
v___y_4162_ = v___y_4210_;
v___y_4163_ = v___y_4215_;
v___y_4164_ = v___y_4211_;
v___y_4165_ = v___y_4204_;
v___y_4166_ = v___y_4213_;
v___y_4167_ = v___y_4207_;
v___y_4168_ = v___y_4214_;
v___y_4169_ = v___y_4205_;
v___y_4170_ = v___y_4212_;
goto v___jp_4155_;
}
else
{
v___y_4156_ = v___y_4203_;
v_interpreted_4157_ = v_interpreted_4217_;
v___y_4158_ = v___y_4208_;
v_valueInconsistency_4159_ = v___x_3937_;
v_trueEqFalse_4160_ = v___x_3933_;
v___y_4161_ = v___y_4209_;
v___y_4162_ = v___y_4210_;
v___y_4163_ = v___y_4215_;
v___y_4164_ = v___y_4211_;
v___y_4165_ = v___y_4204_;
v___y_4166_ = v___y_4213_;
v___y_4167_ = v___y_4207_;
v___y_4168_ = v___y_4214_;
v___y_4169_ = v___y_4205_;
v___y_4170_ = v___y_4212_;
goto v___jp_4155_;
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec_ref(v___y_4208_);
lean_dec_ref(v___y_4203_);
lean_dec(v_a_3930_);
lean_dec(v_a_3927_);
lean_dec_ref(v_proof_3909_);
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
v_a_4222_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4219_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4219_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
else
{
v___y_4173_ = v___y_4203_;
v___y_4174_ = v___y_4208_;
v_valueInconsistency_4175_ = v___x_3937_;
v_trueEqFalse_4176_ = v___x_3933_;
v___y_4177_ = v___y_4209_;
v___y_4178_ = v___y_4210_;
v___y_4179_ = v___y_4215_;
v___y_4180_ = v___y_4211_;
v___y_4181_ = v___y_4204_;
v___y_4182_ = v___y_4213_;
v___y_4183_ = v___y_4207_;
v___y_4184_ = v___y_4214_;
v___y_4185_ = v___y_4205_;
v___y_4186_ = v___y_4212_;
goto v___jp_4172_;
}
}
v___jp_4230_:
{
if (v___y_4243_ == 0)
{
v___y_4173_ = v___y_4231_;
v___y_4174_ = v___y_4236_;
v_valueInconsistency_4175_ = v___x_3933_;
v_trueEqFalse_4176_ = v___x_3933_;
v___y_4177_ = v___y_4235_;
v___y_4178_ = v___y_4237_;
v___y_4179_ = v___y_4242_;
v___y_4180_ = v___y_4238_;
v___y_4181_ = v___y_4232_;
v___y_4182_ = v___y_4240_;
v___y_4183_ = v___y_4234_;
v___y_4184_ = v___y_4241_;
v___y_4185_ = v___y_4233_;
v___y_4186_ = v___y_4239_;
goto v___jp_4172_;
}
else
{
uint8_t v___x_4244_; 
lean_inc_ref(v_root_3931_);
v___x_4244_ = l_Lean_Expr_isTrue(v_root_3931_);
if (v___x_4244_ == 0)
{
uint8_t v___x_4245_; 
lean_inc_ref(v_root_3932_);
v___x_4245_ = l_Lean_Expr_isTrue(v_root_3932_);
if (v___x_4245_ == 0)
{
if (v_isHEq_3910_ == 0)
{
uint8_t v_heqProofs_4246_; 
v_heqProofs_4246_ = lean_ctor_get_uint8(v___y_4231_, sizeof(void*)*11 + 4);
if (v_heqProofs_4246_ == 0)
{
uint8_t v_heqProofs_4247_; 
v_heqProofs_4247_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*11 + 4);
if (v_heqProofs_4247_ == 0)
{
uint8_t v_interpreted_4248_; 
v_interpreted_4248_ = lean_ctor_get_uint8(v___y_4231_, sizeof(void*)*11 + 1);
v___y_4156_ = v___y_4231_;
v_interpreted_4157_ = v_interpreted_4248_;
v___y_4158_ = v___y_4236_;
v_valueInconsistency_4159_ = v___x_3937_;
v_trueEqFalse_4160_ = v___x_3933_;
v___y_4161_ = v___y_4235_;
v___y_4162_ = v___y_4237_;
v___y_4163_ = v___y_4242_;
v___y_4164_ = v___y_4238_;
v___y_4165_ = v___y_4232_;
v___y_4166_ = v___y_4240_;
v___y_4167_ = v___y_4234_;
v___y_4168_ = v___y_4241_;
v___y_4169_ = v___y_4233_;
v___y_4170_ = v___y_4239_;
goto v___jp_4155_;
}
else
{
v___y_4203_ = v___y_4231_;
v___y_4204_ = v___y_4232_;
v___y_4205_ = v___y_4233_;
v___y_4206_ = v___x_4245_;
v___y_4207_ = v___y_4234_;
v___y_4208_ = v___y_4236_;
v___y_4209_ = v___y_4235_;
v___y_4210_ = v___y_4237_;
v___y_4211_ = v___y_4238_;
v___y_4212_ = v___y_4239_;
v___y_4213_ = v___y_4240_;
v___y_4214_ = v___y_4241_;
v___y_4215_ = v___y_4242_;
goto v___jp_4202_;
}
}
else
{
v___y_4203_ = v___y_4231_;
v___y_4204_ = v___y_4232_;
v___y_4205_ = v___y_4233_;
v___y_4206_ = v___x_4245_;
v___y_4207_ = v___y_4234_;
v___y_4208_ = v___y_4236_;
v___y_4209_ = v___y_4235_;
v___y_4210_ = v___y_4237_;
v___y_4211_ = v___y_4238_;
v___y_4212_ = v___y_4239_;
v___y_4213_ = v___y_4240_;
v___y_4214_ = v___y_4241_;
v___y_4215_ = v___y_4242_;
goto v___jp_4202_;
}
}
else
{
v___y_4203_ = v___y_4231_;
v___y_4204_ = v___y_4232_;
v___y_4205_ = v___y_4233_;
v___y_4206_ = v___x_4245_;
v___y_4207_ = v___y_4234_;
v___y_4208_ = v___y_4236_;
v___y_4209_ = v___y_4235_;
v___y_4210_ = v___y_4237_;
v___y_4211_ = v___y_4238_;
v___y_4212_ = v___y_4239_;
v___y_4213_ = v___y_4240_;
v___y_4214_ = v___y_4241_;
v___y_4215_ = v___y_4242_;
goto v___jp_4202_;
}
}
else
{
v___y_4189_ = v___y_4231_;
v___y_4190_ = v___y_4232_;
v___y_4191_ = v___y_4233_;
v___y_4192_ = v___y_4234_;
v___y_4193_ = v___y_4235_;
v___y_4194_ = v___y_4236_;
v___y_4195_ = v___y_4237_;
v___y_4196_ = v___y_4238_;
v___y_4197_ = v___y_4239_;
v___y_4198_ = v___y_4240_;
v___y_4199_ = v___y_4241_;
v___y_4200_ = v___y_4242_;
goto v___jp_4188_;
}
}
else
{
v___y_4189_ = v___y_4231_;
v___y_4190_ = v___y_4232_;
v___y_4191_ = v___y_4233_;
v___y_4192_ = v___y_4234_;
v___y_4193_ = v___y_4235_;
v___y_4194_ = v___y_4236_;
v___y_4195_ = v___y_4237_;
v___y_4196_ = v___y_4238_;
v___y_4197_ = v___y_4239_;
v___y_4198_ = v___y_4240_;
v___y_4199_ = v___y_4241_;
v___y_4200_ = v___y_4242_;
goto v___jp_4188_;
}
}
}
v___jp_4249_:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4260_ = lean_st_ref_get(v___y_4250_);
lean_inc_ref(v_root_3931_);
v___x_4261_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4260_, v_root_3931_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___x_4260_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref(v___x_4261_);
v___x_4263_ = lean_st_ref_get(v___y_4250_);
lean_inc_ref(v_root_3932_);
v___x_4264_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4263_, v_root_3932_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___x_4263_);
if (lean_obj_tag(v___x_4264_) == 0)
{
uint8_t v_interpreted_4265_; 
v_interpreted_4265_ = lean_ctor_get_uint8(v_a_4262_, sizeof(void*)*11 + 1);
if (v_interpreted_4265_ == 0)
{
lean_object* v_a_4266_; 
v_a_4266_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4266_);
lean_dec_ref(v___x_4264_);
v___y_4231_ = v_a_4262_;
v___y_4232_ = v___y_4254_;
v___y_4233_ = v___y_4258_;
v___y_4234_ = v___y_4256_;
v___y_4235_ = v___y_4250_;
v___y_4236_ = v_a_4266_;
v___y_4237_ = v___y_4251_;
v___y_4238_ = v___y_4253_;
v___y_4239_ = v___y_4259_;
v___y_4240_ = v___y_4255_;
v___y_4241_ = v___y_4257_;
v___y_4242_ = v___y_4252_;
v___y_4243_ = v___x_3933_;
goto v___jp_4230_;
}
else
{
lean_object* v_a_4267_; uint8_t v_interpreted_4268_; 
v_a_4267_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4267_);
lean_dec_ref(v___x_4264_);
v_interpreted_4268_ = lean_ctor_get_uint8(v_a_4267_, sizeof(void*)*11 + 1);
v___y_4231_ = v_a_4262_;
v___y_4232_ = v___y_4254_;
v___y_4233_ = v___y_4258_;
v___y_4234_ = v___y_4256_;
v___y_4235_ = v___y_4250_;
v___y_4236_ = v_a_4267_;
v___y_4237_ = v___y_4251_;
v___y_4238_ = v___y_4253_;
v___y_4239_ = v___y_4259_;
v___y_4240_ = v___y_4255_;
v___y_4241_ = v___y_4257_;
v___y_4242_ = v___y_4252_;
v___y_4243_ = v_interpreted_4268_;
goto v___jp_4230_;
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec(v_a_4262_);
lean_dec(v_a_3930_);
lean_dec(v_a_3927_);
lean_dec_ref(v_proof_3909_);
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
v_a_4269_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4264_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4264_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v_a_3930_);
lean_dec(v_a_3927_);
lean_dec_ref(v_proof_3909_);
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
v_a_4277_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4261_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4261_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
else
{
lean_object* v_options_4304_; uint8_t v_hasTrace_4305_; 
lean_dec(v_a_3930_);
lean_dec(v_a_3927_);
lean_dec_ref(v_proof_3909_);
v_options_4304_ = lean_ctor_get(v_a_3919_, 2);
v_hasTrace_4305_ = lean_ctor_get_uint8(v_options_4304_, sizeof(void*)*1);
if (v_hasTrace_4305_ == 0)
{
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
goto v___jp_3922_;
}
else
{
lean_object* v_inheritedTraceOptions_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v_inheritedTraceOptions_4306_ = lean_ctor_get(v_a_3919_, 13);
v___x_4307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4309_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4306_, v_options_4304_, v___x_4308_);
if (v___x_4309_ == 0)
{
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
goto v___jp_3922_;
}
else
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_Meta_Grind_updateLastTag(v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v___x_4311_; 
lean_dec_ref(v___x_4310_);
v___x_4311_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3907_, v_a_3911_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4313_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref(v___x_4311_);
v___x_4313_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3908_, v_a_3911_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref(v___x_4313_);
v___x_4315_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v_a_4312_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
v___x_4317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
lean_ctor_set(v___x_4317_, 1, v_a_4314_);
v___x_4318_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4317_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4307_, v___x_4319_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_dec_ref(v___x_4320_);
goto v___jp_3922_;
}
else
{
return v___x_4320_;
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec(v_a_4312_);
v_a_4321_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4313_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4313_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
lean_dec_ref(v_rhs_3908_);
v_a_4329_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4311_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4311_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
return v___x_4310_;
}
}
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec(v_a_3927_);
lean_dec_ref(v_proof_3909_);
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
v_a_4337_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_3929_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_3929_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
else
{
lean_object* v_a_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4352_; 
lean_dec_ref(v_proof_3909_);
lean_dec_ref(v_rhs_3908_);
lean_dec_ref(v_lhs_3907_);
v_a_4345_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4347_ = v___x_3926_;
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_a_4345_);
lean_dec(v___x_3926_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4350_; 
if (v_isShared_4348_ == 0)
{
v___x_4350_ = v___x_4347_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_a_4345_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
v___jp_3922_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_box(0);
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4353_, lean_object* v_rhs_4354_, lean_object* v_proof_4355_, lean_object* v_isHEq_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
uint8_t v_isHEq_boxed_4368_; lean_object* v_res_4369_; 
v_isHEq_boxed_4368_ = lean_unbox(v_isHEq_4356_);
v_res_4369_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4353_, v_rhs_4354_, v_proof_4355_, v_isHEq_boxed_4368_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
lean_dec(v_a_4366_);
lean_dec_ref(v_a_4365_);
lean_dec(v_a_4364_);
lean_dec_ref(v_a_4363_);
lean_dec(v_a_4362_);
lean_dec_ref(v_a_4361_);
lean_dec(v_a_4360_);
lean_dec_ref(v_a_4359_);
lean_dec(v_a_4358_);
lean_dec(v_a_4357_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4372_){
_start:
{
lean_object* v___x_4374_; lean_object* v_toGoalState_4375_; lean_object* v_mvarId_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4412_; 
v___x_4374_ = lean_st_ref_take(v_a_4372_);
v_toGoalState_4375_ = lean_ctor_get(v___x_4374_, 0);
v_mvarId_4376_ = lean_ctor_get(v___x_4374_, 1);
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4412_ == 0)
{
v___x_4378_ = v___x_4374_;
v_isShared_4379_ = v_isSharedCheck_4412_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_mvarId_4376_);
lean_inc(v_toGoalState_4375_);
lean_dec(v___x_4374_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4412_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v_nextDeclIdx_4380_; lean_object* v_enodeMap_4381_; lean_object* v_exprs_4382_; lean_object* v_parents_4383_; lean_object* v_congrTable_4384_; lean_object* v_appMap_4385_; lean_object* v_indicesFound_4386_; uint8_t v_inconsistent_4387_; lean_object* v_nextIdx_4388_; lean_object* v_newRawFacts_4389_; lean_object* v_facts_4390_; lean_object* v_extThms_4391_; lean_object* v_ematch_4392_; lean_object* v_inj_4393_; lean_object* v_split_4394_; lean_object* v_clean_4395_; lean_object* v_sstates_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4410_; 
v_nextDeclIdx_4380_ = lean_ctor_get(v_toGoalState_4375_, 0);
v_enodeMap_4381_ = lean_ctor_get(v_toGoalState_4375_, 1);
v_exprs_4382_ = lean_ctor_get(v_toGoalState_4375_, 2);
v_parents_4383_ = lean_ctor_get(v_toGoalState_4375_, 3);
v_congrTable_4384_ = lean_ctor_get(v_toGoalState_4375_, 4);
v_appMap_4385_ = lean_ctor_get(v_toGoalState_4375_, 5);
v_indicesFound_4386_ = lean_ctor_get(v_toGoalState_4375_, 6);
v_inconsistent_4387_ = lean_ctor_get_uint8(v_toGoalState_4375_, sizeof(void*)*17);
v_nextIdx_4388_ = lean_ctor_get(v_toGoalState_4375_, 8);
v_newRawFacts_4389_ = lean_ctor_get(v_toGoalState_4375_, 9);
v_facts_4390_ = lean_ctor_get(v_toGoalState_4375_, 10);
v_extThms_4391_ = lean_ctor_get(v_toGoalState_4375_, 11);
v_ematch_4392_ = lean_ctor_get(v_toGoalState_4375_, 12);
v_inj_4393_ = lean_ctor_get(v_toGoalState_4375_, 13);
v_split_4394_ = lean_ctor_get(v_toGoalState_4375_, 14);
v_clean_4395_ = lean_ctor_get(v_toGoalState_4375_, 15);
v_sstates_4396_ = lean_ctor_get(v_toGoalState_4375_, 16);
v_isSharedCheck_4410_ = !lean_is_exclusive(v_toGoalState_4375_);
if (v_isSharedCheck_4410_ == 0)
{
lean_object* v_unused_4411_; 
v_unused_4411_ = lean_ctor_get(v_toGoalState_4375_, 7);
lean_dec(v_unused_4411_);
v___x_4398_ = v_toGoalState_4375_;
v_isShared_4399_ = v_isSharedCheck_4410_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_sstates_4396_);
lean_inc(v_clean_4395_);
lean_inc(v_split_4394_);
lean_inc(v_inj_4393_);
lean_inc(v_ematch_4392_);
lean_inc(v_extThms_4391_);
lean_inc(v_facts_4390_);
lean_inc(v_newRawFacts_4389_);
lean_inc(v_nextIdx_4388_);
lean_inc(v_indicesFound_4386_);
lean_inc(v_appMap_4385_);
lean_inc(v_congrTable_4384_);
lean_inc(v_parents_4383_);
lean_inc(v_exprs_4382_);
lean_inc(v_enodeMap_4381_);
lean_inc(v_nextDeclIdx_4380_);
lean_dec(v_toGoalState_4375_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4410_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 7, v___x_4400_);
v___x_4402_ = v___x_4398_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_nextDeclIdx_4380_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_enodeMap_4381_);
lean_ctor_set(v_reuseFailAlloc_4409_, 2, v_exprs_4382_);
lean_ctor_set(v_reuseFailAlloc_4409_, 3, v_parents_4383_);
lean_ctor_set(v_reuseFailAlloc_4409_, 4, v_congrTable_4384_);
lean_ctor_set(v_reuseFailAlloc_4409_, 5, v_appMap_4385_);
lean_ctor_set(v_reuseFailAlloc_4409_, 6, v_indicesFound_4386_);
lean_ctor_set(v_reuseFailAlloc_4409_, 7, v___x_4400_);
lean_ctor_set(v_reuseFailAlloc_4409_, 8, v_nextIdx_4388_);
lean_ctor_set(v_reuseFailAlloc_4409_, 9, v_newRawFacts_4389_);
lean_ctor_set(v_reuseFailAlloc_4409_, 10, v_facts_4390_);
lean_ctor_set(v_reuseFailAlloc_4409_, 11, v_extThms_4391_);
lean_ctor_set(v_reuseFailAlloc_4409_, 12, v_ematch_4392_);
lean_ctor_set(v_reuseFailAlloc_4409_, 13, v_inj_4393_);
lean_ctor_set(v_reuseFailAlloc_4409_, 14, v_split_4394_);
lean_ctor_set(v_reuseFailAlloc_4409_, 15, v_clean_4395_);
lean_ctor_set(v_reuseFailAlloc_4409_, 16, v_sstates_4396_);
lean_ctor_set_uint8(v_reuseFailAlloc_4409_, sizeof(void*)*17, v_inconsistent_4387_);
v___x_4402_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4404_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4402_);
v___x_4404_ = v___x_4378_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4402_);
lean_ctor_set(v_reuseFailAlloc_4408_, 1, v_mvarId_4376_);
v___x_4404_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4405_ = lean_st_ref_set(v_a_4372_, v___x_4404_);
v___x_4406_ = lean_box(0);
v___x_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
return v___x_4407_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4413_);
lean_dec(v_a_4413_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4416_);
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_);
lean_dec(v_a_4437_);
lean_dec_ref(v_a_4436_);
lean_dec(v_a_4435_);
lean_dec_ref(v_a_4434_);
lean_dec(v_a_4433_);
lean_dec_ref(v_a_4432_);
lean_dec(v_a_4431_);
lean_dec_ref(v_a_4430_);
lean_dec(v_a_4429_);
lean_dec(v_a_4428_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4440_){
_start:
{
lean_object* v___x_4442_; lean_object* v_toGoalState_4443_; lean_object* v_newFacts_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; uint8_t v___x_4448_; 
v___x_4442_ = lean_st_ref_get(v_a_4440_);
v_toGoalState_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc_ref(v_toGoalState_4443_);
lean_dec(v___x_4442_);
v_newFacts_4444_ = lean_ctor_get(v_toGoalState_4443_, 7);
lean_inc_ref(v_newFacts_4444_);
lean_dec_ref(v_toGoalState_4443_);
v___x_4445_ = lean_array_get_size(v_newFacts_4444_);
v___x_4446_ = lean_unsigned_to_nat(1u);
v___x_4447_ = lean_nat_sub(v___x_4445_, v___x_4446_);
v___x_4448_ = lean_nat_dec_lt(v___x_4447_, v___x_4445_);
if (v___x_4448_ == 0)
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_dec(v___x_4447_);
lean_dec_ref(v_newFacts_4444_);
v___x_4449_ = lean_box(0);
v___x_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4449_);
return v___x_4450_;
}
else
{
lean_object* v___x_4451_; lean_object* v_toGoalState_4452_; lean_object* v_mvarId_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4490_; 
v___x_4451_ = lean_st_ref_take(v_a_4440_);
v_toGoalState_4452_ = lean_ctor_get(v___x_4451_, 0);
v_mvarId_4453_ = lean_ctor_get(v___x_4451_, 1);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4455_ = v___x_4451_;
v_isShared_4456_ = v_isSharedCheck_4490_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_mvarId_4453_);
lean_inc(v_toGoalState_4452_);
lean_dec(v___x_4451_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4490_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v_nextDeclIdx_4457_; lean_object* v_enodeMap_4458_; lean_object* v_exprs_4459_; lean_object* v_parents_4460_; lean_object* v_congrTable_4461_; lean_object* v_appMap_4462_; lean_object* v_indicesFound_4463_; lean_object* v_newFacts_4464_; uint8_t v_inconsistent_4465_; lean_object* v_nextIdx_4466_; lean_object* v_newRawFacts_4467_; lean_object* v_facts_4468_; lean_object* v_extThms_4469_; lean_object* v_ematch_4470_; lean_object* v_inj_4471_; lean_object* v_split_4472_; lean_object* v_clean_4473_; lean_object* v_sstates_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4489_; 
v_nextDeclIdx_4457_ = lean_ctor_get(v_toGoalState_4452_, 0);
v_enodeMap_4458_ = lean_ctor_get(v_toGoalState_4452_, 1);
v_exprs_4459_ = lean_ctor_get(v_toGoalState_4452_, 2);
v_parents_4460_ = lean_ctor_get(v_toGoalState_4452_, 3);
v_congrTable_4461_ = lean_ctor_get(v_toGoalState_4452_, 4);
v_appMap_4462_ = lean_ctor_get(v_toGoalState_4452_, 5);
v_indicesFound_4463_ = lean_ctor_get(v_toGoalState_4452_, 6);
v_newFacts_4464_ = lean_ctor_get(v_toGoalState_4452_, 7);
v_inconsistent_4465_ = lean_ctor_get_uint8(v_toGoalState_4452_, sizeof(void*)*17);
v_nextIdx_4466_ = lean_ctor_get(v_toGoalState_4452_, 8);
v_newRawFacts_4467_ = lean_ctor_get(v_toGoalState_4452_, 9);
v_facts_4468_ = lean_ctor_get(v_toGoalState_4452_, 10);
v_extThms_4469_ = lean_ctor_get(v_toGoalState_4452_, 11);
v_ematch_4470_ = lean_ctor_get(v_toGoalState_4452_, 12);
v_inj_4471_ = lean_ctor_get(v_toGoalState_4452_, 13);
v_split_4472_ = lean_ctor_get(v_toGoalState_4452_, 14);
v_clean_4473_ = lean_ctor_get(v_toGoalState_4452_, 15);
v_sstates_4474_ = lean_ctor_get(v_toGoalState_4452_, 16);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_toGoalState_4452_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4476_ = v_toGoalState_4452_;
v_isShared_4477_ = v_isSharedCheck_4489_;
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
lean_inc(v_newFacts_4464_);
lean_inc(v_indicesFound_4463_);
lean_inc(v_appMap_4462_);
lean_inc(v_congrTable_4461_);
lean_inc(v_parents_4460_);
lean_inc(v_exprs_4459_);
lean_inc(v_enodeMap_4458_);
lean_inc(v_nextDeclIdx_4457_);
lean_dec(v_toGoalState_4452_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4489_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4478_; lean_object* v___x_4480_; 
v___x_4478_ = lean_array_pop(v_newFacts_4464_);
if (v_isShared_4477_ == 0)
{
lean_ctor_set(v___x_4476_, 7, v___x_4478_);
v___x_4480_ = v___x_4476_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_nextDeclIdx_4457_);
lean_ctor_set(v_reuseFailAlloc_4488_, 1, v_enodeMap_4458_);
lean_ctor_set(v_reuseFailAlloc_4488_, 2, v_exprs_4459_);
lean_ctor_set(v_reuseFailAlloc_4488_, 3, v_parents_4460_);
lean_ctor_set(v_reuseFailAlloc_4488_, 4, v_congrTable_4461_);
lean_ctor_set(v_reuseFailAlloc_4488_, 5, v_appMap_4462_);
lean_ctor_set(v_reuseFailAlloc_4488_, 6, v_indicesFound_4463_);
lean_ctor_set(v_reuseFailAlloc_4488_, 7, v___x_4478_);
lean_ctor_set(v_reuseFailAlloc_4488_, 8, v_nextIdx_4466_);
lean_ctor_set(v_reuseFailAlloc_4488_, 9, v_newRawFacts_4467_);
lean_ctor_set(v_reuseFailAlloc_4488_, 10, v_facts_4468_);
lean_ctor_set(v_reuseFailAlloc_4488_, 11, v_extThms_4469_);
lean_ctor_set(v_reuseFailAlloc_4488_, 12, v_ematch_4470_);
lean_ctor_set(v_reuseFailAlloc_4488_, 13, v_inj_4471_);
lean_ctor_set(v_reuseFailAlloc_4488_, 14, v_split_4472_);
lean_ctor_set(v_reuseFailAlloc_4488_, 15, v_clean_4473_);
lean_ctor_set(v_reuseFailAlloc_4488_, 16, v_sstates_4474_);
lean_ctor_set_uint8(v_reuseFailAlloc_4488_, sizeof(void*)*17, v_inconsistent_4465_);
v___x_4480_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
lean_object* v___x_4482_; 
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v___x_4480_);
v___x_4482_ = v___x_4455_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4480_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v_mvarId_4453_);
v___x_4482_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4483_ = lean_st_ref_set(v_a_4440_, v___x_4482_);
v___x_4484_ = lean_array_fget(v_newFacts_4444_, v___x_4447_);
lean_dec(v___x_4447_);
lean_dec_ref(v_newFacts_4444_);
v___x_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
v___x_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4485_);
return v___x_4486_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4491_);
lean_dec(v_a_4491_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v___x_4505_; 
v___x_4505_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4494_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4518_, lean_object* v_rhs_4519_, lean_object* v_proof_4520_, uint8_t v_isHEq_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v___x_4533_; 
v___x_4533_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4518_, v_rhs_4519_, v_proof_4520_, v_isHEq_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v___x_4534_; 
lean_dec_ref(v___x_4533_);
lean_inc(v_a_4531_);
lean_inc_ref(v_a_4530_);
lean_inc(v_a_4529_);
lean_inc_ref(v_a_4528_);
lean_inc(v_a_4527_);
lean_inc_ref(v_a_4526_);
lean_inc(v_a_4525_);
lean_inc_ref(v_a_4524_);
lean_inc(v_a_4523_);
lean_inc(v_a_4522_);
v___x_4534_ = lean_grind_process_new_facts(v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
return v___x_4534_;
}
else
{
return v___x_4533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4535_, lean_object* v_rhs_4536_, lean_object* v_proof_4537_, lean_object* v_isHEq_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_){
_start:
{
uint8_t v_isHEq_boxed_4550_; lean_object* v_res_4551_; 
v_isHEq_boxed_4550_ = lean_unbox(v_isHEq_4538_);
v_res_4551_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4535_, v_rhs_4536_, v_proof_4537_, v_isHEq_boxed_4550_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec(v_a_4539_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4552_, lean_object* v_rhs_4553_, lean_object* v_proof_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_){
_start:
{
uint8_t v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = 0;
v___x_4567_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4552_, v_rhs_4553_, v_proof_4554_, v___x_4566_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4568_, lean_object* v_rhs_4569_, lean_object* v_proof_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4568_, v_rhs_4569_, v_proof_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
lean_dec(v_a_4580_);
lean_dec_ref(v_a_4579_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
lean_dec(v_a_4574_);
lean_dec_ref(v_a_4573_);
lean_dec(v_a_4572_);
lean_dec(v_a_4571_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4583_, lean_object* v_rhs_4584_, lean_object* v_proof_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
uint8_t v___x_4597_; lean_object* v___x_4598_; 
v___x_4597_ = 1;
v___x_4598_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4583_, v_rhs_4584_, v_proof_4585_, v___x_4597_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_);
return v___x_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4599_, lean_object* v_rhs_4600_, lean_object* v_proof_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4599_, v_rhs_4600_, v_proof_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
lean_dec(v_a_4605_);
lean_dec_ref(v_a_4604_);
lean_dec(v_a_4603_);
lean_dec(v_a_4602_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4614_, lean_object* v_a_4615_){
_start:
{
lean_object* v___x_4617_; lean_object* v_toGoalState_4618_; lean_object* v_mvarId_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4655_; 
v___x_4617_ = lean_st_ref_take(v_a_4615_);
v_toGoalState_4618_ = lean_ctor_get(v___x_4617_, 0);
v_mvarId_4619_ = lean_ctor_get(v___x_4617_, 1);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4621_ = v___x_4617_;
v_isShared_4622_ = v_isSharedCheck_4655_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_mvarId_4619_);
lean_inc(v_toGoalState_4618_);
lean_dec(v___x_4617_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4655_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v_nextDeclIdx_4623_; lean_object* v_enodeMap_4624_; lean_object* v_exprs_4625_; lean_object* v_parents_4626_; lean_object* v_congrTable_4627_; lean_object* v_appMap_4628_; lean_object* v_indicesFound_4629_; lean_object* v_newFacts_4630_; uint8_t v_inconsistent_4631_; lean_object* v_nextIdx_4632_; lean_object* v_newRawFacts_4633_; lean_object* v_facts_4634_; lean_object* v_extThms_4635_; lean_object* v_ematch_4636_; lean_object* v_inj_4637_; lean_object* v_split_4638_; lean_object* v_clean_4639_; lean_object* v_sstates_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4654_; 
v_nextDeclIdx_4623_ = lean_ctor_get(v_toGoalState_4618_, 0);
v_enodeMap_4624_ = lean_ctor_get(v_toGoalState_4618_, 1);
v_exprs_4625_ = lean_ctor_get(v_toGoalState_4618_, 2);
v_parents_4626_ = lean_ctor_get(v_toGoalState_4618_, 3);
v_congrTable_4627_ = lean_ctor_get(v_toGoalState_4618_, 4);
v_appMap_4628_ = lean_ctor_get(v_toGoalState_4618_, 5);
v_indicesFound_4629_ = lean_ctor_get(v_toGoalState_4618_, 6);
v_newFacts_4630_ = lean_ctor_get(v_toGoalState_4618_, 7);
v_inconsistent_4631_ = lean_ctor_get_uint8(v_toGoalState_4618_, sizeof(void*)*17);
v_nextIdx_4632_ = lean_ctor_get(v_toGoalState_4618_, 8);
v_newRawFacts_4633_ = lean_ctor_get(v_toGoalState_4618_, 9);
v_facts_4634_ = lean_ctor_get(v_toGoalState_4618_, 10);
v_extThms_4635_ = lean_ctor_get(v_toGoalState_4618_, 11);
v_ematch_4636_ = lean_ctor_get(v_toGoalState_4618_, 12);
v_inj_4637_ = lean_ctor_get(v_toGoalState_4618_, 13);
v_split_4638_ = lean_ctor_get(v_toGoalState_4618_, 14);
v_clean_4639_ = lean_ctor_get(v_toGoalState_4618_, 15);
v_sstates_4640_ = lean_ctor_get(v_toGoalState_4618_, 16);
v_isSharedCheck_4654_ = !lean_is_exclusive(v_toGoalState_4618_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4642_ = v_toGoalState_4618_;
v_isShared_4643_ = v_isSharedCheck_4654_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_sstates_4640_);
lean_inc(v_clean_4639_);
lean_inc(v_split_4638_);
lean_inc(v_inj_4637_);
lean_inc(v_ematch_4636_);
lean_inc(v_extThms_4635_);
lean_inc(v_facts_4634_);
lean_inc(v_newRawFacts_4633_);
lean_inc(v_nextIdx_4632_);
lean_inc(v_newFacts_4630_);
lean_inc(v_indicesFound_4629_);
lean_inc(v_appMap_4628_);
lean_inc(v_congrTable_4627_);
lean_inc(v_parents_4626_);
lean_inc(v_exprs_4625_);
lean_inc(v_enodeMap_4624_);
lean_inc(v_nextDeclIdx_4623_);
lean_dec(v_toGoalState_4618_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4654_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4644_; lean_object* v___x_4646_; 
v___x_4644_ = l_Lean_PersistentArray_push___redArg(v_facts_4634_, v_fact_4614_);
if (v_isShared_4643_ == 0)
{
lean_ctor_set(v___x_4642_, 10, v___x_4644_);
v___x_4646_ = v___x_4642_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_nextDeclIdx_4623_);
lean_ctor_set(v_reuseFailAlloc_4653_, 1, v_enodeMap_4624_);
lean_ctor_set(v_reuseFailAlloc_4653_, 2, v_exprs_4625_);
lean_ctor_set(v_reuseFailAlloc_4653_, 3, v_parents_4626_);
lean_ctor_set(v_reuseFailAlloc_4653_, 4, v_congrTable_4627_);
lean_ctor_set(v_reuseFailAlloc_4653_, 5, v_appMap_4628_);
lean_ctor_set(v_reuseFailAlloc_4653_, 6, v_indicesFound_4629_);
lean_ctor_set(v_reuseFailAlloc_4653_, 7, v_newFacts_4630_);
lean_ctor_set(v_reuseFailAlloc_4653_, 8, v_nextIdx_4632_);
lean_ctor_set(v_reuseFailAlloc_4653_, 9, v_newRawFacts_4633_);
lean_ctor_set(v_reuseFailAlloc_4653_, 10, v___x_4644_);
lean_ctor_set(v_reuseFailAlloc_4653_, 11, v_extThms_4635_);
lean_ctor_set(v_reuseFailAlloc_4653_, 12, v_ematch_4636_);
lean_ctor_set(v_reuseFailAlloc_4653_, 13, v_inj_4637_);
lean_ctor_set(v_reuseFailAlloc_4653_, 14, v_split_4638_);
lean_ctor_set(v_reuseFailAlloc_4653_, 15, v_clean_4639_);
lean_ctor_set(v_reuseFailAlloc_4653_, 16, v_sstates_4640_);
lean_ctor_set_uint8(v_reuseFailAlloc_4653_, sizeof(void*)*17, v_inconsistent_4631_);
v___x_4646_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4645_;
}
v_reusejp_4645_:
{
lean_object* v___x_4648_; 
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 0, v___x_4646_);
v___x_4648_ = v___x_4621_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4646_);
lean_ctor_set(v_reuseFailAlloc_4652_, 1, v_mvarId_4619_);
v___x_4648_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4649_ = lean_st_ref_set(v_a_4615_, v___x_4648_);
v___x_4650_ = lean_box(0);
v___x_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4650_);
return v___x_4651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4656_, v_a_4657_);
lean_dec(v_a_4657_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4660_, v_a_4661_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_);
lean_dec(v_a_4683_);
lean_dec_ref(v_a_4682_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
lean_dec(v_a_4675_);
lean_dec(v_a_4674_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4686_, lean_object* v_rhs_4687_, lean_object* v_proof_4688_, lean_object* v_generation_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_){
_start:
{
lean_object* v___x_4701_; 
lean_inc_ref(v_rhs_4687_);
lean_inc_ref(v_lhs_4686_);
v___x_4701_ = l_Lean_Meta_mkEq(v_lhs_4686_, v_rhs_4687_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4713_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc_n(v_a_4702_, 2);
lean_dec_ref(v___x_4701_);
v___x_4703_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4702_, v_a_4690_);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4713_ == 0)
{
lean_object* v_unused_4714_; 
v_unused_4714_ = lean_ctor_get(v___x_4703_, 0);
lean_dec(v_unused_4714_);
v___x_4705_ = v___x_4703_;
v_isShared_4706_ = v_isSharedCheck_4713_;
goto v_resetjp_4704_;
}
else
{
lean_dec(v___x_4703_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4713_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
lean_ctor_set_tag(v___x_4705_, 1);
lean_ctor_set(v___x_4705_, 0, v_a_4702_);
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4702_);
v___x_4708_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_object* v___x_4709_; 
lean_inc(v_a_4699_);
lean_inc_ref(v_a_4698_);
lean_inc(v_a_4697_);
lean_inc_ref(v_a_4696_);
lean_inc(v_a_4695_);
lean_inc_ref(v_a_4694_);
lean_inc(v_a_4693_);
lean_inc_ref(v_a_4692_);
lean_inc(v_a_4691_);
lean_inc(v_a_4690_);
lean_inc_ref(v___x_4708_);
lean_inc(v_generation_4689_);
lean_inc_ref(v_lhs_4686_);
v___x_4709_ = lean_grind_internalize(v_lhs_4686_, v_generation_4689_, v___x_4708_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v___x_4710_; 
lean_dec_ref(v___x_4709_);
lean_inc(v_a_4699_);
lean_inc_ref(v_a_4698_);
lean_inc(v_a_4697_);
lean_inc_ref(v_a_4696_);
lean_inc(v_a_4695_);
lean_inc_ref(v_a_4694_);
lean_inc(v_a_4693_);
lean_inc_ref(v_a_4692_);
lean_inc(v_a_4691_);
lean_inc(v_a_4690_);
lean_inc_ref(v_rhs_4687_);
v___x_4710_ = lean_grind_internalize(v_rhs_4687_, v_generation_4689_, v___x_4708_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v___x_4711_; 
lean_dec_ref(v___x_4710_);
v___x_4711_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4686_, v_rhs_4687_, v_proof_4688_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
return v___x_4711_;
}
else
{
lean_dec_ref(v_proof_4688_);
lean_dec_ref(v_rhs_4687_);
lean_dec_ref(v_lhs_4686_);
return v___x_4710_;
}
}
else
{
lean_dec_ref(v___x_4708_);
lean_dec(v_generation_4689_);
lean_dec_ref(v_proof_4688_);
lean_dec_ref(v_rhs_4687_);
lean_dec_ref(v_lhs_4686_);
return v___x_4709_;
}
}
}
}
else
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4722_; 
lean_dec(v_generation_4689_);
lean_dec_ref(v_proof_4688_);
lean_dec_ref(v_rhs_4687_);
lean_dec_ref(v_lhs_4686_);
v_a_4715_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4717_ = v___x_4701_;
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v___x_4701_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4720_; 
if (v_isShared_4718_ == 0)
{
v___x_4720_ = v___x_4717_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4715_);
v___x_4720_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
return v___x_4720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4723_, lean_object* v_rhs_4724_, lean_object* v_proof_4725_, lean_object* v_generation_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4723_, v_rhs_4724_, v_proof_4725_, v_generation_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_);
lean_dec(v_a_4736_);
lean_dec_ref(v_a_4735_);
lean_dec(v_a_4734_);
lean_dec_ref(v_a_4733_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
lean_dec(v_a_4730_);
lean_dec_ref(v_a_4729_);
lean_dec(v_a_4728_);
lean_dec(v_a_4727_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4739_, lean_object* v_generation_4740_, lean_object* v_p_4741_, uint8_t v_isNeg_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4754_ = lean_box(0);
lean_inc(v_a_4752_);
lean_inc_ref(v_a_4751_);
lean_inc(v_a_4750_);
lean_inc_ref(v_a_4749_);
lean_inc(v_a_4748_);
lean_inc_ref(v_a_4747_);
lean_inc(v_a_4746_);
lean_inc_ref(v_a_4745_);
lean_inc(v_a_4744_);
lean_inc(v_a_4743_);
lean_inc_ref(v_p_4741_);
v___x_4755_ = lean_grind_internalize(v_p_4741_, v_generation_4740_, v___x_4754_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_dec_ref(v___x_4755_);
if (v_isNeg_4742_ == 0)
{
lean_object* v___x_4756_; 
v___x_4756_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4747_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; lean_object* v___x_4758_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
lean_inc(v_a_4757_);
lean_dec_ref(v___x_4756_);
v___x_4758_ = l_Lean_Meta_mkEqTrue(v_proof_4739_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4760_; 
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
lean_inc(v_a_4759_);
lean_dec_ref(v___x_4758_);
v___x_4760_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4741_, v_a_4757_, v_a_4759_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
return v___x_4760_;
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec(v_a_4757_);
lean_dec_ref(v_p_4741_);
v_a_4761_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4758_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4758_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
else
{
lean_object* v_a_4769_; lean_object* v___x_4771_; uint8_t v_isShared_4772_; uint8_t v_isSharedCheck_4776_; 
lean_dec_ref(v_p_4741_);
lean_dec_ref(v_proof_4739_);
v_a_4769_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4771_ = v___x_4756_;
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
else
{
lean_inc(v_a_4769_);
lean_dec(v___x_4756_);
v___x_4771_ = lean_box(0);
v_isShared_4772_ = v_isSharedCheck_4776_;
goto v_resetjp_4770_;
}
v_resetjp_4770_:
{
lean_object* v___x_4774_; 
if (v_isShared_4772_ == 0)
{
v___x_4774_ = v___x_4771_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
}
else
{
lean_object* v___x_4777_; 
v___x_4777_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4747_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v___x_4779_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_a_4778_);
lean_dec_ref(v___x_4777_);
v___x_4779_ = l_Lean_Meta_mkEqFalse(v_proof_4739_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v___x_4781_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_a_4780_);
lean_dec_ref(v___x_4779_);
v___x_4781_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4741_, v_a_4778_, v_a_4780_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
return v___x_4781_;
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_dec(v_a_4778_);
lean_dec_ref(v_p_4741_);
v_a_4782_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4779_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4779_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
lean_dec_ref(v_p_4741_);
lean_dec_ref(v_proof_4739_);
v_a_4790_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4777_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4777_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4741_);
lean_dec_ref(v_proof_4739_);
return v___x_4755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4798_, lean_object* v_generation_4799_, lean_object* v_p_4800_, lean_object* v_isNeg_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_){
_start:
{
uint8_t v_isNeg_boxed_4813_; lean_object* v_res_4814_; 
v_isNeg_boxed_4813_ = lean_unbox(v_isNeg_4801_);
v_res_4814_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4798_, v_generation_4799_, v_p_4800_, v_isNeg_boxed_4813_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_);
lean_dec(v_a_4811_);
lean_dec_ref(v_a_4810_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec(v_a_4802_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4815_, lean_object* v_generation_4816_, lean_object* v_p_4817_, lean_object* v_lhs_4818_, lean_object* v_rhs_4819_, uint8_t v_isNeg_4820_, uint8_t v_isHEq_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
if (v_isNeg_4820_ == 0)
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
lean_inc_ref(v_p_4817_);
v___x_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4833_, 0, v_p_4817_);
lean_inc(v_a_4831_);
lean_inc_ref(v_a_4830_);
lean_inc(v_a_4829_);
lean_inc_ref(v_a_4828_);
lean_inc(v_a_4827_);
lean_inc_ref(v_a_4826_);
lean_inc(v_a_4825_);
lean_inc_ref(v_a_4824_);
lean_inc(v_a_4823_);
lean_inc(v_a_4822_);
lean_inc_ref(v___x_4833_);
lean_inc(v_generation_4816_);
lean_inc_ref(v_lhs_4818_);
v___x_4834_ = lean_grind_internalize(v_lhs_4818_, v_generation_4816_, v___x_4833_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4834_) == 0)
{
lean_object* v___x_4835_; 
lean_dec_ref(v___x_4834_);
lean_inc(v_a_4831_);
lean_inc_ref(v_a_4830_);
lean_inc(v_a_4829_);
lean_inc_ref(v_a_4828_);
lean_inc(v_a_4827_);
lean_inc_ref(v_a_4826_);
lean_inc(v_a_4825_);
lean_inc_ref(v_a_4824_);
lean_inc(v_a_4823_);
lean_inc(v_a_4822_);
lean_inc_ref(v_rhs_4819_);
v___x_4835_ = lean_grind_internalize(v_rhs_4819_, v_generation_4816_, v___x_4833_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
lean_dec_ref(v___x_4835_);
v___x_4836_ = lean_box(0);
v___x_4837_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4817_, v___x_4836_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4837_) == 0)
{
lean_object* v___x_4838_; 
lean_dec_ref(v___x_4837_);
v___x_4838_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4818_, v_rhs_4819_, v_proof_4815_, v_isHEq_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
return v___x_4838_;
}
else
{
lean_dec_ref(v_rhs_4819_);
lean_dec_ref(v_lhs_4818_);
lean_dec_ref(v_proof_4815_);
return v___x_4837_;
}
}
else
{
lean_dec_ref(v_rhs_4819_);
lean_dec_ref(v_lhs_4818_);
lean_dec_ref(v_p_4817_);
lean_dec_ref(v_proof_4815_);
return v___x_4835_;
}
}
else
{
lean_dec_ref(v___x_4833_);
lean_dec_ref(v_rhs_4819_);
lean_dec_ref(v_lhs_4818_);
lean_dec_ref(v_p_4817_);
lean_dec(v_generation_4816_);
lean_dec_ref(v_proof_4815_);
return v___x_4834_;
}
}
else
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
lean_dec_ref(v_rhs_4819_);
lean_dec_ref(v_lhs_4818_);
v___x_4839_ = lean_box(0);
lean_inc(v_a_4831_);
lean_inc_ref(v_a_4830_);
lean_inc(v_a_4829_);
lean_inc_ref(v_a_4828_);
lean_inc(v_a_4827_);
lean_inc_ref(v_a_4826_);
lean_inc(v_a_4825_);
lean_inc_ref(v_a_4824_);
lean_inc(v_a_4823_);
lean_inc(v_a_4822_);
lean_inc_ref(v_p_4817_);
v___x_4840_ = lean_grind_internalize(v_p_4817_, v_generation_4816_, v___x_4839_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v___x_4841_; 
lean_dec_ref(v___x_4840_);
v___x_4841_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4826_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v_a_4842_; lean_object* v___x_4843_; 
v_a_4842_ = lean_ctor_get(v___x_4841_, 0);
lean_inc(v_a_4842_);
lean_dec_ref(v___x_4841_);
v___x_4843_ = l_Lean_Meta_mkEqFalse(v_proof_4815_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v_a_4844_; lean_object* v___x_4845_; 
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
lean_inc(v_a_4844_);
lean_dec_ref(v___x_4843_);
v___x_4845_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4817_, v_a_4842_, v_a_4844_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
return v___x_4845_;
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
lean_dec(v_a_4842_);
lean_dec_ref(v_p_4817_);
v_a_4846_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4843_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4843_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
lean_dec_ref(v_p_4817_);
lean_dec_ref(v_proof_4815_);
v_a_4854_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4841_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4841_);
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
lean_dec_ref(v_p_4817_);
lean_dec_ref(v_proof_4815_);
return v___x_4840_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4862_ = _args[0];
lean_object* v_generation_4863_ = _args[1];
lean_object* v_p_4864_ = _args[2];
lean_object* v_lhs_4865_ = _args[3];
lean_object* v_rhs_4866_ = _args[4];
lean_object* v_isNeg_4867_ = _args[5];
lean_object* v_isHEq_4868_ = _args[6];
lean_object* v_a_4869_ = _args[7];
lean_object* v_a_4870_ = _args[8];
lean_object* v_a_4871_ = _args[9];
lean_object* v_a_4872_ = _args[10];
lean_object* v_a_4873_ = _args[11];
lean_object* v_a_4874_ = _args[12];
lean_object* v_a_4875_ = _args[13];
lean_object* v_a_4876_ = _args[14];
lean_object* v_a_4877_ = _args[15];
lean_object* v_a_4878_ = _args[16];
lean_object* v_a_4879_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4880_; uint8_t v_isHEq_boxed_4881_; lean_object* v_res_4882_; 
v_isNeg_boxed_4880_ = lean_unbox(v_isNeg_4867_);
v_isHEq_boxed_4881_ = lean_unbox(v_isHEq_4868_);
v_res_4882_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4862_, v_generation_4863_, v_p_4864_, v_lhs_4865_, v_rhs_4866_, v_isNeg_boxed_4880_, v_isHEq_boxed_4881_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_);
lean_dec(v_a_4878_);
lean_dec_ref(v_a_4877_);
lean_dec(v_a_4876_);
lean_dec_ref(v_a_4875_);
lean_dec(v_a_4874_);
lean_dec_ref(v_a_4873_);
lean_dec(v_a_4872_);
lean_dec_ref(v_a_4871_);
lean_dec(v_a_4870_);
lean_dec(v_a_4869_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4886_, lean_object* v_generation_4887_, lean_object* v_p_4888_, uint8_t v_isNeg_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_){
_start:
{
lean_object* v___x_4901_; 
lean_inc_ref(v_p_4888_);
v___x_4901_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4888_, v_a_4897_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v_a_4902_; lean_object* v___x_4903_; uint8_t v___x_4904_; 
v_a_4902_ = lean_ctor_get(v___x_4901_, 0);
lean_inc(v_a_4902_);
lean_dec_ref(v___x_4901_);
v___x_4903_ = l_Lean_Expr_cleanupAnnotations(v_a_4902_);
v___x_4904_ = l_Lean_Expr_isApp(v___x_4903_);
if (v___x_4904_ == 0)
{
lean_object* v___x_4905_; 
lean_dec_ref(v___x_4903_);
v___x_4905_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4886_, v_generation_4887_, v_p_4888_, v_isNeg_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
return v___x_4905_;
}
else
{
lean_object* v_arg_4906_; lean_object* v___x_4907_; uint8_t v___x_4908_; 
v_arg_4906_ = lean_ctor_get(v___x_4903_, 1);
lean_inc_ref(v_arg_4906_);
v___x_4907_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4903_);
v___x_4908_ = l_Lean_Expr_isApp(v___x_4907_);
if (v___x_4908_ == 0)
{
lean_object* v___x_4909_; 
lean_dec_ref(v___x_4907_);
lean_dec_ref(v_arg_4906_);
v___x_4909_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4886_, v_generation_4887_, v_p_4888_, v_isNeg_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
return v___x_4909_;
}
else
{
lean_object* v_arg_4910_; lean_object* v___x_4911_; uint8_t v___x_4912_; 
v_arg_4910_ = lean_ctor_get(v___x_4907_, 1);
lean_inc_ref(v_arg_4910_);
v___x_4911_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4907_);
v___x_4912_ = l_Lean_Expr_isApp(v___x_4911_);
if (v___x_4912_ == 0)
{
lean_object* v___x_4913_; 
lean_dec_ref(v___x_4911_);
lean_dec_ref(v_arg_4910_);
lean_dec_ref(v_arg_4906_);
v___x_4913_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4886_, v_generation_4887_, v_p_4888_, v_isNeg_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
return v___x_4913_;
}
else
{
lean_object* v_arg_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; uint8_t v___x_4917_; 
v_arg_4914_ = lean_ctor_get(v___x_4911_, 1);
lean_inc_ref(v_arg_4914_);
v___x_4915_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4911_);
v___x_4916_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_4917_ = l_Lean_Expr_isConstOf(v___x_4915_, v___x_4916_);
if (v___x_4917_ == 0)
{
uint8_t v___x_4918_; 
lean_dec_ref(v_arg_4910_);
v___x_4918_ = l_Lean_Expr_isApp(v___x_4915_);
if (v___x_4918_ == 0)
{
lean_object* v___x_4919_; 
lean_dec_ref(v___x_4915_);
lean_dec_ref(v_arg_4914_);
lean_dec_ref(v_arg_4906_);
v___x_4919_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4886_, v_generation_4887_, v_p_4888_, v_isNeg_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
return v___x_4919_;
}
else
{
lean_object* v___x_4920_; lean_object* v___x_4921_; uint8_t v___x_4922_; 
v___x_4920_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4915_);
v___x_4921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_4922_ = l_Lean_Expr_isConstOf(v___x_4920_, v___x_4921_);
lean_dec_ref(v___x_4920_);
if (v___x_4922_ == 0)
{
lean_object* v___x_4923_; 
lean_dec_ref(v_arg_4914_);
lean_dec_ref(v_arg_4906_);
v___x_4923_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4886_, v_generation_4887_, v_p_4888_, v_isNeg_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
return v___x_4923_;
}
else
{
lean_object* v___x_4924_; 
v___x_4924_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4886_, v_generation_4887_, v_p_4888_, v_arg_4914_, v_arg_4906_, v_isNeg_4889_, v___x_4922_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
return v___x_4924_;
}
}
}
else
{
uint8_t v___x_4925_; 
lean_dec_ref(v___x_4915_);
v___x_4925_ = l_Lean_Expr_isProp(v_arg_4914_);
lean_dec_ref(v_arg_4914_);
if (v___x_4925_ == 0)
{
lean_object* v___x_4926_; 
v___x_4926_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4886_, v_generation_4887_, v_p_4888_, v_arg_4910_, v_arg_4906_, v_isNeg_4889_, v___x_4925_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
return v___x_4926_;
}
else
{
lean_object* v___x_4927_; 
lean_dec_ref(v_arg_4910_);
lean_dec_ref(v_arg_4906_);
v___x_4927_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4886_, v_generation_4887_, v_p_4888_, v_isNeg_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_);
return v___x_4927_;
}
}
}
}
}
}
else
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
lean_dec_ref(v_p_4888_);
lean_dec(v_generation_4887_);
lean_dec_ref(v_proof_4886_);
v_a_4928_ = lean_ctor_get(v___x_4901_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4901_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4901_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4928_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_4936_, lean_object* v_generation_4937_, lean_object* v_p_4938_, lean_object* v_isNeg_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_){
_start:
{
uint8_t v_isNeg_boxed_4951_; lean_object* v_res_4952_; 
v_isNeg_boxed_4951_ = lean_unbox(v_isNeg_4939_);
v_res_4952_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4936_, v_generation_4937_, v_p_4938_, v_isNeg_boxed_4951_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_);
lean_dec(v_a_4949_);
lean_dec_ref(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_a_4946_);
lean_dec(v_a_4945_);
lean_dec_ref(v_a_4944_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
lean_dec(v_a_4941_);
lean_dec(v_a_4940_);
return v_res_4952_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_4961_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4962_ = l_Lean_Name_append(v___x_4961_, v___x_4960_);
return v___x_4962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_4963_, lean_object* v_proof_4964_, lean_object* v_generation_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_){
_start:
{
lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4982_; lean_object* v___y_4983_; lean_object* v___y_4984_; lean_object* v___y_4985_; lean_object* v___y_4986_; lean_object* v___y_4987_; lean_object* v___y_4991_; lean_object* v___y_4992_; lean_object* v___y_4993_; lean_object* v___y_4994_; lean_object* v___y_4995_; lean_object* v___y_4996_; lean_object* v___y_4997_; lean_object* v___y_4998_; lean_object* v___y_4999_; lean_object* v___y_5000_; lean_object* v___x_5008_; lean_object* v_options_5009_; uint8_t v_hasTrace_5010_; 
lean_inc_ref(v_fact_4963_);
v___x_5008_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4963_, v_a_4966_);
lean_dec_ref(v___x_5008_);
v_options_5009_ = lean_ctor_get(v_a_4974_, 2);
v_hasTrace_5010_ = lean_ctor_get_uint8(v_options_5009_, sizeof(void*)*1);
if (v_hasTrace_5010_ == 0)
{
v___y_4991_ = v_a_4966_;
v___y_4992_ = v_a_4967_;
v___y_4993_ = v_a_4968_;
v___y_4994_ = v_a_4969_;
v___y_4995_ = v_a_4970_;
v___y_4996_ = v_a_4971_;
v___y_4997_ = v_a_4972_;
v___y_4998_ = v_a_4973_;
v___y_4999_ = v_a_4974_;
v___y_5000_ = v_a_4975_;
goto v___jp_4990_;
}
else
{
lean_object* v_inheritedTraceOptions_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; uint8_t v___x_5014_; 
v_inheritedTraceOptions_5011_ = lean_ctor_get(v_a_4974_, 13);
v___x_5012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5013_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5011_, v_options_5009_, v___x_5013_);
if (v___x_5014_ == 0)
{
v___y_4991_ = v_a_4966_;
v___y_4992_ = v_a_4967_;
v___y_4993_ = v_a_4968_;
v___y_4994_ = v_a_4969_;
v___y_4995_ = v_a_4970_;
v___y_4996_ = v_a_4971_;
v___y_4997_ = v_a_4972_;
v___y_4998_ = v_a_4973_;
v___y_4999_ = v_a_4974_;
v___y_5000_ = v_a_4975_;
goto v___jp_4990_;
}
else
{
lean_object* v___x_5015_; 
v___x_5015_ = l_Lean_Meta_Grind_updateLastTag(v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_);
if (lean_obj_tag(v___x_5015_) == 0)
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
lean_dec_ref(v___x_5015_);
lean_inc_ref(v_fact_4963_);
v___x_5016_ = l_Lean_MessageData_ofExpr(v_fact_4963_);
v___x_5017_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5012_, v___x_5016_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_dec_ref(v___x_5017_);
v___y_4991_ = v_a_4966_;
v___y_4992_ = v_a_4967_;
v___y_4993_ = v_a_4968_;
v___y_4994_ = v_a_4969_;
v___y_4995_ = v_a_4970_;
v___y_4996_ = v_a_4971_;
v___y_4997_ = v_a_4972_;
v___y_4998_ = v_a_4973_;
v___y_4999_ = v_a_4974_;
v___y_5000_ = v_a_4975_;
goto v___jp_4990_;
}
else
{
lean_dec(v_generation_4965_);
lean_dec_ref(v_proof_4964_);
lean_dec_ref(v_fact_4963_);
return v___x_5017_;
}
}
else
{
lean_dec(v_generation_4965_);
lean_dec_ref(v_proof_4964_);
lean_dec_ref(v_fact_4963_);
return v___x_5015_;
}
}
}
v___jp_4977_:
{
uint8_t v___x_4988_; lean_object* v___x_4989_; 
v___x_4988_ = 0;
v___x_4989_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4964_, v_generation_4965_, v_fact_4963_, v___x_4988_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
return v___x_4989_;
}
v___jp_4990_:
{
lean_object* v___x_5001_; uint8_t v___x_5002_; 
lean_inc_ref(v_fact_4963_);
v___x_5001_ = l_Lean_Expr_cleanupAnnotations(v_fact_4963_);
v___x_5002_ = l_Lean_Expr_isApp(v___x_5001_);
if (v___x_5002_ == 0)
{
lean_dec_ref(v___x_5001_);
v___y_4978_ = v___y_4991_;
v___y_4979_ = v___y_4992_;
v___y_4980_ = v___y_4993_;
v___y_4981_ = v___y_4994_;
v___y_4982_ = v___y_4995_;
v___y_4983_ = v___y_4996_;
v___y_4984_ = v___y_4997_;
v___y_4985_ = v___y_4998_;
v___y_4986_ = v___y_4999_;
v___y_4987_ = v___y_5000_;
goto v___jp_4977_;
}
else
{
lean_object* v_arg_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; uint8_t v___x_5006_; 
v_arg_5003_ = lean_ctor_get(v___x_5001_, 1);
lean_inc_ref(v_arg_5003_);
v___x_5004_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5001_);
v___x_5005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5006_ = l_Lean_Expr_isConstOf(v___x_5004_, v___x_5005_);
lean_dec_ref(v___x_5004_);
if (v___x_5006_ == 0)
{
lean_dec_ref(v_arg_5003_);
v___y_4978_ = v___y_4991_;
v___y_4979_ = v___y_4992_;
v___y_4980_ = v___y_4993_;
v___y_4981_ = v___y_4994_;
v___y_4982_ = v___y_4995_;
v___y_4983_ = v___y_4996_;
v___y_4984_ = v___y_4997_;
v___y_4985_ = v___y_4998_;
v___y_4986_ = v___y_4999_;
v___y_4987_ = v___y_5000_;
goto v___jp_4977_;
}
else
{
lean_object* v___x_5007_; 
lean_dec_ref(v_fact_4963_);
v___x_5007_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4964_, v_generation_4965_, v_arg_5003_, v___x_5006_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_);
return v___x_5007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5018_, lean_object* v_proof_5019_, lean_object* v_generation_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5018_, v_proof_5019_, v_generation_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_);
lean_dec(v_a_5030_);
lean_dec_ref(v_a_5029_);
lean_dec(v_a_5028_);
lean_dec_ref(v_a_5027_);
lean_dec(v_a_5026_);
lean_dec_ref(v_a_5025_);
lean_dec(v_a_5024_);
lean_dec_ref(v_a_5023_);
lean_dec(v_a_5022_);
lean_dec(v_a_5021_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
lean_object* v___x_5047_; 
v___x_5047_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5036_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; uint8_t v___x_5049_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_a_5048_);
lean_dec_ref(v___x_5047_);
v___x_5049_ = lean_unbox(v_a_5048_);
lean_dec(v_a_5048_);
if (v___x_5049_ == 0)
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
v___x_5050_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5051_ = l_Lean_Core_checkSystem(v___x_5050_, v___y_5044_, v___y_5045_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v___x_5052_; 
lean_dec_ref(v___x_5051_);
v___x_5052_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5036_);
if (lean_obj_tag(v___x_5052_) == 0)
{
lean_object* v_a_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5089_; 
v_a_5053_ = lean_ctor_get(v___x_5052_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5052_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5055_ = v___x_5052_;
v_isShared_5056_ = v_isSharedCheck_5089_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_a_5053_);
lean_dec(v___x_5052_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5089_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
if (lean_obj_tag(v_a_5053_) == 1)
{
lean_object* v_val_5057_; 
lean_del_object(v___x_5055_);
v_val_5057_ = lean_ctor_get(v_a_5053_, 0);
lean_inc(v_val_5057_);
lean_dec_ref(v_a_5053_);
if (lean_obj_tag(v_val_5057_) == 0)
{
lean_object* v_lhs_5058_; lean_object* v_rhs_5059_; lean_object* v_proof_5060_; uint8_t v_isHEq_5061_; lean_object* v___x_5062_; 
v_lhs_5058_ = lean_ctor_get(v_val_5057_, 0);
lean_inc_ref(v_lhs_5058_);
v_rhs_5059_ = lean_ctor_get(v_val_5057_, 1);
lean_inc_ref(v_rhs_5059_);
v_proof_5060_ = lean_ctor_get(v_val_5057_, 2);
lean_inc_ref(v_proof_5060_);
v_isHEq_5061_ = lean_ctor_get_uint8(v_val_5057_, sizeof(void*)*3);
lean_dec_ref(v_val_5057_);
v___x_5062_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5058_, v_rhs_5059_, v_proof_5060_, v_isHEq_5061_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_dec_ref(v___x_5062_);
goto _start;
}
else
{
lean_object* v_a_5064_; lean_object* v___x_5066_; uint8_t v_isShared_5067_; uint8_t v_isSharedCheck_5071_; 
v_a_5064_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5071_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5071_ == 0)
{
v___x_5066_ = v___x_5062_;
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
else
{
lean_inc(v_a_5064_);
lean_dec(v___x_5062_);
v___x_5066_ = lean_box(0);
v_isShared_5067_ = v_isSharedCheck_5071_;
goto v_resetjp_5065_;
}
v_resetjp_5065_:
{
lean_object* v___x_5069_; 
if (v_isShared_5067_ == 0)
{
v___x_5069_ = v___x_5066_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5064_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
}
else
{
lean_object* v_prop_5072_; lean_object* v_proof_5073_; lean_object* v_generation_5074_; lean_object* v___x_5075_; 
v_prop_5072_ = lean_ctor_get(v_val_5057_, 0);
lean_inc_ref(v_prop_5072_);
v_proof_5073_ = lean_ctor_get(v_val_5057_, 1);
lean_inc_ref(v_proof_5073_);
v_generation_5074_ = lean_ctor_get(v_val_5057_, 2);
lean_inc(v_generation_5074_);
lean_dec_ref(v_val_5057_);
v___x_5075_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5072_, v_proof_5073_, v_generation_5074_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_dec_ref(v___x_5075_);
goto _start;
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
v_a_5077_ = lean_ctor_get(v___x_5075_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5075_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5075_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
}
else
{
lean_object* v___x_5085_; lean_object* v___x_5087_; 
lean_dec(v_a_5053_);
v___x_5085_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5056_ == 0)
{
lean_ctor_set(v___x_5055_, 0, v___x_5085_);
v___x_5087_ = v___x_5055_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v___x_5085_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
else
{
lean_object* v_a_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5097_; 
v_a_5090_ = lean_ctor_get(v___x_5052_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5052_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5092_ = v___x_5052_;
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_a_5090_);
lean_dec(v___x_5052_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5095_; 
if (v_isShared_5093_ == 0)
{
v___x_5095_ = v___x_5092_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
}
else
{
lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5105_; 
v_a_5098_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5100_ = v___x_5051_;
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_5051_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v___x_5103_; 
if (v_isShared_5101_ == 0)
{
v___x_5103_ = v___x_5100_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_a_5098_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
}
}
else
{
lean_object* v___x_5106_; 
v___x_5106_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5036_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5114_; 
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5114_ == 0)
{
lean_object* v_unused_5115_; 
v_unused_5115_ = lean_ctor_get(v___x_5106_, 0);
lean_dec(v_unused_5115_);
v___x_5108_ = v___x_5106_;
v_isShared_5109_ = v_isSharedCheck_5114_;
goto v_resetjp_5107_;
}
else
{
lean_dec(v___x_5106_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5114_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5110_; lean_object* v___x_5112_; 
v___x_5110_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5109_ == 0)
{
lean_ctor_set(v___x_5108_, 0, v___x_5110_);
v___x_5112_ = v___x_5108_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5110_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
v_a_5116_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5106_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5106_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
}
else
{
lean_object* v_a_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5131_; 
v_a_5124_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5126_ = v___x_5047_;
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
else
{
lean_inc(v_a_5124_);
lean_dec(v___x_5047_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5131_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5129_; 
if (v_isShared_5127_ == 0)
{
v___x_5129_ = v___x_5126_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_a_5124_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
return v___x_5129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
lean_dec(v___y_5137_);
lean_dec_ref(v___y_5136_);
lean_dec(v___y_5135_);
lean_dec_ref(v___y_5134_);
lean_dec(v___y_5133_);
lean_dec(v___y_5132_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_, lean_object* v_a_5152_, lean_object* v_a_5153_){
_start:
{
lean_object* v___x_5155_; 
v___x_5155_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_, v_a_5151_, v_a_5152_, v_a_5153_);
lean_dec(v_a_5153_);
lean_dec_ref(v_a_5152_);
lean_dec(v_a_5151_);
lean_dec_ref(v_a_5150_);
lean_dec(v_a_5149_);
lean_dec_ref(v_a_5148_);
lean_dec(v_a_5147_);
lean_dec_ref(v_a_5146_);
lean_dec(v_a_5145_);
lean_dec(v_a_5144_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5169_; 
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5158_ = v___x_5155_;
v_isShared_5159_ = v_isSharedCheck_5169_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5155_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5169_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v_fst_5160_; 
v_fst_5160_ = lean_ctor_get(v_a_5156_, 0);
lean_inc(v_fst_5160_);
lean_dec(v_a_5156_);
if (lean_obj_tag(v_fst_5160_) == 0)
{
lean_object* v___x_5161_; lean_object* v___x_5163_; 
v___x_5161_ = lean_box(0);
if (v_isShared_5159_ == 0)
{
lean_ctor_set(v___x_5158_, 0, v___x_5161_);
v___x_5163_ = v___x_5158_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5164_; 
v_reuseFailAlloc_5164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5164_, 0, v___x_5161_);
v___x_5163_ = v_reuseFailAlloc_5164_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
return v___x_5163_;
}
}
else
{
lean_object* v_val_5165_; lean_object* v___x_5167_; 
v_val_5165_ = lean_ctor_get(v_fst_5160_, 0);
lean_inc(v_val_5165_);
lean_dec_ref(v_fst_5160_);
if (v_isShared_5159_ == 0)
{
lean_ctor_set(v___x_5158_, 0, v_val_5165_);
v___x_5167_ = v___x_5158_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_val_5165_);
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
else
{
lean_object* v_a_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5177_; 
v_a_5170_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5172_ = v___x_5155_;
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_a_5170_);
lean_dec(v___x_5155_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5175_; 
if (v_isShared_5173_ == 0)
{
v___x_5175_ = v___x_5172_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_a_5170_);
v___x_5175_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
return v___x_5175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = lean_grind_process_new_facts(v_a_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_b_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_){
_start:
{
lean_object* v___x_5202_; 
v___x_5202_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
return v___x_5202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_b_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
lean_object* v_res_5215_; 
v_res_5215_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_b_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
lean_dec(v___y_5211_);
lean_dec_ref(v___y_5210_);
lean_dec(v___y_5209_);
lean_dec_ref(v___y_5208_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
lean_dec(v___y_5205_);
lean_dec(v___y_5204_);
lean_dec_ref(v_b_5203_);
return v_res_5215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5216_, lean_object* v_proof_5217_, lean_object* v_generation_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_){
_start:
{
uint8_t v___x_5230_; 
lean_inc_ref(v_fact_5216_);
v___x_5230_ = l_Lean_Expr_isTrue(v_fact_5216_);
if (v___x_5230_ == 0)
{
lean_object* v___x_5231_; 
v___x_5231_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5219_);
if (lean_obj_tag(v___x_5231_) == 0)
{
lean_object* v_a_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5243_; 
v_a_5232_ = lean_ctor_get(v___x_5231_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5231_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5234_ = v___x_5231_;
v_isShared_5235_ = v_isSharedCheck_5243_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_a_5232_);
lean_dec(v___x_5231_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5243_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
uint8_t v___x_5236_; 
v___x_5236_ = lean_unbox(v_a_5232_);
lean_dec(v_a_5232_);
if (v___x_5236_ == 0)
{
lean_object* v___x_5237_; lean_object* v___x_5238_; 
lean_del_object(v___x_5234_);
v___x_5237_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5219_);
lean_dec_ref(v___x_5237_);
v___x_5238_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5216_, v_proof_5217_, v_generation_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_);
return v___x_5238_;
}
else
{
lean_object* v___x_5239_; lean_object* v___x_5241_; 
lean_dec(v_generation_5218_);
lean_dec_ref(v_proof_5217_);
lean_dec_ref(v_fact_5216_);
v___x_5239_ = lean_box(0);
if (v_isShared_5235_ == 0)
{
lean_ctor_set(v___x_5234_, 0, v___x_5239_);
v___x_5241_ = v___x_5234_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v___x_5239_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
else
{
lean_object* v_a_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5251_; 
lean_dec(v_generation_5218_);
lean_dec_ref(v_proof_5217_);
lean_dec_ref(v_fact_5216_);
v_a_5244_ = lean_ctor_get(v___x_5231_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v___x_5231_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5246_ = v___x_5231_;
v_isShared_5247_ = v_isSharedCheck_5251_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_a_5244_);
lean_dec(v___x_5231_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5251_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v___x_5249_; 
if (v_isShared_5247_ == 0)
{
v___x_5249_ = v___x_5246_;
goto v_reusejp_5248_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v_a_5244_);
v___x_5249_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5248_;
}
v_reusejp_5248_:
{
return v___x_5249_;
}
}
}
}
else
{
lean_object* v___x_5252_; lean_object* v___x_5253_; 
lean_dec(v_generation_5218_);
lean_dec_ref(v_proof_5217_);
lean_dec_ref(v_fact_5216_);
v___x_5252_ = lean_box(0);
v___x_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5253_, 0, v___x_5252_);
return v___x_5253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5254_, lean_object* v_proof_5255_, lean_object* v_generation_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_){
_start:
{
lean_object* v_res_5268_; 
v_res_5268_ = l_Lean_Meta_Grind_add(v_fact_5254_, v_proof_5255_, v_generation_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_);
lean_dec(v_a_5266_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec_ref(v_a_5263_);
lean_dec(v_a_5262_);
lean_dec_ref(v_a_5261_);
lean_dec(v_a_5260_);
lean_dec_ref(v_a_5259_);
lean_dec(v_a_5258_);
lean_dec(v_a_5257_);
return v_res_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5269_, lean_object* v_generation_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_){
_start:
{
lean_object* v___x_5282_; 
lean_inc(v_fvarId_5269_);
v___x_5282_ = l_Lean_FVarId_getType___redArg(v_fvarId_5269_, v_a_5277_, v_a_5279_, v_a_5280_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_object* v_a_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; 
v_a_5283_ = lean_ctor_get(v___x_5282_, 0);
lean_inc(v_a_5283_);
lean_dec_ref(v___x_5282_);
v___x_5284_ = l_Lean_mkFVar(v_fvarId_5269_);
v___x_5285_ = l_Lean_Meta_Grind_add(v_a_5283_, v___x_5284_, v_generation_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_, v_a_5280_);
return v___x_5285_;
}
else
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5293_; 
lean_dec(v_generation_5270_);
lean_dec(v_fvarId_5269_);
v_a_5286_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5288_ = v___x_5282_;
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___x_5282_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5291_; 
if (v_isShared_5289_ == 0)
{
v___x_5291_ = v___x_5288_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5294_, lean_object* v_generation_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_){
_start:
{
lean_object* v_res_5307_; 
v_res_5307_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5294_, v_generation_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_);
lean_dec(v_a_5305_);
lean_dec_ref(v_a_5304_);
lean_dec(v_a_5303_);
lean_dec_ref(v_a_5302_);
lean_dec(v_a_5301_);
lean_dec_ref(v_a_5300_);
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec(v_a_5297_);
lean_dec(v_a_5296_);
return v_res_5307_;
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
