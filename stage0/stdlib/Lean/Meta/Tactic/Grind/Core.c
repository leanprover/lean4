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
lean_object* v_ref_192_; lean_object* v___x_193_; lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_239_; 
v_ref_192_ = lean_ctor_get(v___y_189_, 5);
v___x_193_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msg_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_239_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_239_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_239_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v_traceState_199_; lean_object* v_env_200_; lean_object* v_nextMacroScope_201_; lean_object* v_ngen_202_; lean_object* v_auxDeclNGen_203_; lean_object* v_cache_204_; lean_object* v_messages_205_; lean_object* v_infoState_206_; lean_object* v_snapshotTasks_207_; lean_object* v_newDecls_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_238_; 
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
v_newDecls_208_ = lean_ctor_get(v___x_198_, 9);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_238_ == 0)
{
v___x_210_ = v___x_198_;
v_isShared_211_ = v_isSharedCheck_238_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_newDecls_208_);
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
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_238_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
uint64_t v_tid_212_; lean_object* v_traces_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_237_; 
v_tid_212_ = lean_ctor_get_uint64(v_traceState_199_, sizeof(void*)*1);
v_traces_213_ = lean_ctor_get(v_traceState_199_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_traceState_199_);
if (v_isSharedCheck_237_ == 0)
{
v___x_215_ = v_traceState_199_;
v_isShared_216_ = v_isSharedCheck_237_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_traces_213_);
lean_dec(v_traceState_199_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_237_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; double v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_217_ = lean_box(0);
v___x_218_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0);
v___x_219_ = 0;
v___x_220_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
v___x_221_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_221_, 0, v_cls_185_);
lean_ctor_set(v___x_221_, 1, v___x_217_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
lean_ctor_set_float(v___x_221_, sizeof(void*)*3, v___x_218_);
lean_ctor_set_float(v___x_221_, sizeof(void*)*3 + 8, v___x_218_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*3 + 16, v___x_219_);
v___x_222_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2));
v___x_223_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v_a_194_);
lean_ctor_set(v___x_223_, 2, v___x_222_);
lean_inc(v_ref_192_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v_ref_192_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = l_Lean_PersistentArray_push___redArg(v_traces_213_, v___x_224_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_225_);
v___x_227_ = v___x_215_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_225_);
lean_ctor_set_uint64(v_reuseFailAlloc_236_, sizeof(void*)*1, v_tid_212_);
v___x_227_ = v_reuseFailAlloc_236_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 4, v___x_227_);
v___x_229_ = v___x_210_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_env_200_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_nextMacroScope_201_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_ngen_202_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_auxDeclNGen_203_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_235_, 5, v_cache_204_);
lean_ctor_set(v_reuseFailAlloc_235_, 6, v_messages_205_);
lean_ctor_set(v_reuseFailAlloc_235_, 7, v_infoState_206_);
lean_ctor_set(v_reuseFailAlloc_235_, 8, v_snapshotTasks_207_);
lean_ctor_set(v_reuseFailAlloc_235_, 9, v_newDecls_208_);
v___x_229_ = v_reuseFailAlloc_235_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = lean_st_ref_set(v___y_190_, v___x_229_);
v___x_231_ = lean_box(0);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_231_);
v___x_233_ = v___x_196_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object* v_cls_240_, lean_object* v_msg_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_240_, v_msg_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(lean_object* v___x_248_, lean_object* v_xs_249_, lean_object* v_v_250_, lean_object* v_i_251_){
_start:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_array_get_size(v_xs_249_);
v___x_253_ = lean_nat_dec_lt(v_i_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_i_251_);
lean_dec_ref(v_v_250_);
v___x_254_ = lean_box(0);
return v___x_254_;
}
else
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_array_fget_borrowed(v_xs_249_, v_i_251_);
lean_inc_ref(v_v_250_);
lean_inc(v___x_255_);
v___x_256_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_248_, v___x_255_, v_v_250_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_i_251_, v___x_257_);
lean_dec(v_i_251_);
v_i_251_ = v___x_258_;
goto _start;
}
else
{
lean_object* v___x_260_; 
lean_dec_ref(v_v_250_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v_i_251_);
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v___x_261_, lean_object* v_xs_262_, lean_object* v_v_263_, lean_object* v_i_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_261_, v_xs_262_, v_v_263_, v_i_264_);
lean_dec_ref(v_xs_262_);
lean_dec_ref(v___x_261_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(lean_object* v___x_266_, lean_object* v_xs_267_, lean_object* v_v_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_266_, v_xs_267_, v_v_268_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1___boxed(lean_object* v___x_271_, lean_object* v_xs_272_, lean_object* v_v_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_271_, v_xs_272_, v_v_273_);
lean_dec_ref(v_xs_272_);
lean_dec_ref(v___x_271_);
return v_res_274_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; 
v___x_275_ = ((size_t)5ULL);
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_shift_left(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static size_t _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; 
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__0);
v___x_280_ = lean_usize_sub(v___x_279_, v___x_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* v___x_281_, lean_object* v_x_282_, size_t v_x_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
lean_object* v_es_285_; lean_object* v___x_286_; size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; lean_object* v_j_290_; lean_object* v_entry_291_; 
v_es_285_ = lean_ctor_get(v_x_282_, 0);
v___x_286_ = lean_box(2);
v___x_287_ = ((size_t)5ULL);
v___x_288_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_289_ = lean_usize_land(v_x_283_, v___x_288_);
v_j_290_ = lean_usize_to_nat(v___x_289_);
v_entry_291_ = lean_array_get(v___x_286_, v_es_285_, v_j_290_);
switch(lean_obj_tag(v_entry_291_))
{
case 0:
{
lean_object* v_key_292_; uint8_t v___x_293_; 
v_key_292_ = lean_ctor_get(v_entry_291_, 0);
lean_inc(v_key_292_);
lean_dec_ref(v_entry_291_);
v___x_293_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_281_, v_x_284_, v_key_292_);
if (v___x_293_ == 0)
{
lean_dec(v_j_290_);
return v_x_282_;
}
else
{
lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
lean_inc_ref(v_es_285_);
v_isSharedCheck_301_ = !lean_is_exclusive(v_x_282_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v_x_282_, 0);
lean_dec(v_unused_302_);
v___x_295_ = v_x_282_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_dec(v_x_282_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_array_set(v_es_285_, v_j_290_, v___x_286_);
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
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_336_; 
lean_inc_ref(v_es_285_);
v_isSharedCheck_336_ = !lean_is_exclusive(v_x_282_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; 
v_unused_337_ = lean_ctor_get(v_x_282_, 0);
lean_dec(v_unused_337_);
v___x_304_ = v_x_282_;
v_isShared_305_ = v_isSharedCheck_336_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_x_282_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_336_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_node_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_335_; 
v_node_306_ = lean_ctor_get(v_entry_291_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_entry_291_);
if (v_isSharedCheck_335_ == 0)
{
v___x_308_ = v_entry_291_;
v_isShared_309_ = v_isSharedCheck_335_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_node_306_);
lean_dec(v_entry_291_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_335_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_entries_310_; size_t v___x_311_; lean_object* v_newNode_312_; lean_object* v___x_313_; 
v_entries_310_ = lean_array_set(v_es_285_, v_j_290_, v___x_286_);
v___x_311_ = lean_usize_shift_right(v_x_283_, v___x_287_);
v_newNode_312_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_281_, v_node_306_, v___x_311_, v_x_284_);
lean_inc_ref(v_newNode_312_);
v___x_313_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_312_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v___x_315_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v_newNode_312_);
v___x_315_ = v___x_308_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_newNode_312_);
v___x_315_ = v_reuseFailAlloc_320_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_array_set(v_entries_310_, v_j_290_, v___x_315_);
lean_dec(v_j_290_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_316_);
v___x_318_ = v___x_304_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_val_321_; lean_object* v_fst_322_; lean_object* v_snd_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_newNode_312_);
lean_del_object(v___x_308_);
v_val_321_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_val_321_);
lean_dec_ref(v___x_313_);
v_fst_322_ = lean_ctor_get(v_val_321_, 0);
v_snd_323_ = lean_ctor_get(v_val_321_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_val_321_);
if (v_isSharedCheck_334_ == 0)
{
v___x_325_ = v_val_321_;
v_isShared_326_ = v_isSharedCheck_334_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_snd_323_);
lean_inc(v_fst_322_);
lean_dec(v_val_321_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_334_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_fst_322_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_snd_323_);
v___x_328_ = v_reuseFailAlloc_333_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_329_ = lean_array_set(v_entries_310_, v_j_290_, v___x_328_);
lean_dec(v_j_290_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_329_);
v___x_331_ = v___x_304_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
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
lean_dec_ref(v_x_284_);
return v_x_282_;
}
}
}
else
{
lean_object* v_ks_338_; lean_object* v_vs_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_353_; 
v_ks_338_ = lean_ctor_get(v_x_282_, 0);
v_vs_339_ = lean_ctor_get(v_x_282_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_x_282_);
if (v_isSharedCheck_353_ == 0)
{
v___x_341_ = v_x_282_;
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_vs_339_);
lean_inc(v_ks_338_);
lean_dec(v_x_282_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; 
v___x_343_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_281_, v_ks_338_, v_x_284_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_345_; 
if (v_isShared_342_ == 0)
{
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_ks_338_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_vs_339_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
else
{
lean_object* v_val_347_; lean_object* v_keys_x27_348_; lean_object* v_vals_x27_349_; lean_object* v___x_351_; 
v_val_347_ = lean_ctor_get(v___x_343_, 0);
lean_inc_n(v_val_347_, 2);
lean_dec_ref(v___x_343_);
v_keys_x27_348_ = l_Array_eraseIdx___redArg(v_ks_338_, v_val_347_);
v_vals_x27_349_ = l_Array_eraseIdx___redArg(v_vs_339_, v_val_347_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v_vals_x27_349_);
lean_ctor_set(v___x_341_, 0, v_keys_x27_348_);
v___x_351_ = v___x_341_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_keys_x27_348_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_vals_x27_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* v___x_354_, lean_object* v_x_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
size_t v_x_28310__boxed_358_; lean_object* v_res_359_; 
v_x_28310__boxed_358_ = lean_unbox_usize(v_x_356_);
lean_dec(v_x_356_);
v_res_359_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_354_, v_x_355_, v_x_28310__boxed_358_, v_x_357_);
lean_dec_ref(v___x_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
uint64_t v___x_363_; size_t v_h_364_; lean_object* v___x_365_; 
lean_inc_ref(v_x_362_);
v___x_363_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_360_, v_x_362_);
v_h_364_ = lean_uint64_to_usize(v___x_363_);
v___x_365_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_360_, v_x_361_, v_h_364_, v_x_362_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg___boxed(lean_object* v___x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_366_, v_x_367_, v_x_368_);
lean_dec_ref(v___x_366_);
return v_res_369_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_381_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_382_ = l_Lean_Name_append(v___x_381_, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object* v_as_x27_386_, lean_object* v_b_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
if (lean_obj_tag(v_as_x27_386_) == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v_b_387_);
return v___x_399_;
}
else
{
lean_object* v_head_400_; lean_object* v_tail_401_; lean_object* v___x_402_; lean_object* v___y_404_; uint8_t v_a_444_; uint8_t v___x_457_; 
v_head_400_ = lean_ctor_get(v_as_x27_386_, 0);
v_tail_401_ = lean_ctor_get(v_as_x27_386_, 1);
v___x_402_ = lean_box(0);
v___x_457_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_400_);
if (v___x_457_ == 0)
{
v_a_444_ = v___x_457_;
goto v___jp_443_;
}
else
{
lean_object* v___x_458_; 
lean_inc(v_head_400_);
v___x_458_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_400_, v___y_388_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; uint8_t v___x_460_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref(v___x_458_);
v___x_460_ = lean_unbox(v_a_459_);
lean_dec(v_a_459_);
v_a_444_ = v___x_460_;
goto v___jp_443_;
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_458_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_458_);
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
v___jp_403_:
{
lean_object* v___x_405_; lean_object* v_toGoalState_406_; lean_object* v_mvarId_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_442_; 
v___x_405_ = lean_st_ref_take(v___y_404_);
v_toGoalState_406_ = lean_ctor_get(v___x_405_, 0);
v_mvarId_407_ = lean_ctor_get(v___x_405_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_442_ == 0)
{
v___x_409_ = v___x_405_;
v_isShared_410_ = v_isSharedCheck_442_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_mvarId_407_);
lean_inc(v_toGoalState_406_);
lean_dec(v___x_405_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_442_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_nextDeclIdx_411_; lean_object* v_enodeMap_412_; lean_object* v_exprs_413_; lean_object* v_parents_414_; lean_object* v_congrTable_415_; lean_object* v_appMap_416_; lean_object* v_indicesFound_417_; lean_object* v_newFacts_418_; uint8_t v_inconsistent_419_; lean_object* v_nextIdx_420_; lean_object* v_newRawFacts_421_; lean_object* v_facts_422_; lean_object* v_extThms_423_; lean_object* v_ematch_424_; lean_object* v_inj_425_; lean_object* v_split_426_; lean_object* v_clean_427_; lean_object* v_sstates_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_441_; 
v_nextDeclIdx_411_ = lean_ctor_get(v_toGoalState_406_, 0);
v_enodeMap_412_ = lean_ctor_get(v_toGoalState_406_, 1);
v_exprs_413_ = lean_ctor_get(v_toGoalState_406_, 2);
v_parents_414_ = lean_ctor_get(v_toGoalState_406_, 3);
v_congrTable_415_ = lean_ctor_get(v_toGoalState_406_, 4);
v_appMap_416_ = lean_ctor_get(v_toGoalState_406_, 5);
v_indicesFound_417_ = lean_ctor_get(v_toGoalState_406_, 6);
v_newFacts_418_ = lean_ctor_get(v_toGoalState_406_, 7);
v_inconsistent_419_ = lean_ctor_get_uint8(v_toGoalState_406_, sizeof(void*)*17);
v_nextIdx_420_ = lean_ctor_get(v_toGoalState_406_, 8);
v_newRawFacts_421_ = lean_ctor_get(v_toGoalState_406_, 9);
v_facts_422_ = lean_ctor_get(v_toGoalState_406_, 10);
v_extThms_423_ = lean_ctor_get(v_toGoalState_406_, 11);
v_ematch_424_ = lean_ctor_get(v_toGoalState_406_, 12);
v_inj_425_ = lean_ctor_get(v_toGoalState_406_, 13);
v_split_426_ = lean_ctor_get(v_toGoalState_406_, 14);
v_clean_427_ = lean_ctor_get(v_toGoalState_406_, 15);
v_sstates_428_ = lean_ctor_get(v_toGoalState_406_, 16);
v_isSharedCheck_441_ = !lean_is_exclusive(v_toGoalState_406_);
if (v_isSharedCheck_441_ == 0)
{
v___x_430_ = v_toGoalState_406_;
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
lean_inc(v_newFacts_418_);
lean_inc(v_indicesFound_417_);
lean_inc(v_appMap_416_);
lean_inc(v_congrTable_415_);
lean_inc(v_parents_414_);
lean_inc(v_exprs_413_);
lean_inc(v_enodeMap_412_);
lean_inc(v_nextDeclIdx_411_);
lean_dec(v_toGoalState_406_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_441_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
lean_inc(v_head_400_);
v___x_432_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_412_, v_congrTable_415_, v_head_400_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 4, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_nextDeclIdx_411_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_enodeMap_412_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_exprs_413_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_parents_414_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_appMap_416_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_indicesFound_417_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_newFacts_418_);
lean_ctor_set(v_reuseFailAlloc_440_, 8, v_nextIdx_420_);
lean_ctor_set(v_reuseFailAlloc_440_, 9, v_newRawFacts_421_);
lean_ctor_set(v_reuseFailAlloc_440_, 10, v_facts_422_);
lean_ctor_set(v_reuseFailAlloc_440_, 11, v_extThms_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 12, v_ematch_424_);
lean_ctor_set(v_reuseFailAlloc_440_, 13, v_inj_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 14, v_split_426_);
lean_ctor_set(v_reuseFailAlloc_440_, 15, v_clean_427_);
lean_ctor_set(v_reuseFailAlloc_440_, 16, v_sstates_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_440_, sizeof(void*)*17, v_inconsistent_419_);
v___x_434_ = v_reuseFailAlloc_440_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_434_);
v___x_436_ = v___x_409_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_mvarId_407_);
v___x_436_ = v_reuseFailAlloc_439_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; 
v___x_437_ = lean_st_ref_set(v___y_404_, v___x_436_);
v_as_x27_386_ = v_tail_401_;
v_b_387_ = v___x_402_;
goto _start;
}
}
}
}
}
v___jp_443_:
{
if (v_a_444_ == 0)
{
v_as_x27_386_ = v_tail_401_;
v_b_387_ = v___x_402_;
goto _start;
}
else
{
lean_object* v_options_446_; uint8_t v_hasTrace_447_; 
v_options_446_ = lean_ctor_get(v___y_396_, 2);
v_hasTrace_447_ = lean_ctor_get_uint8(v_options_446_, sizeof(void*)*1);
if (v_hasTrace_447_ == 0)
{
v___y_404_ = v___y_388_;
goto v___jp_403_;
}
else
{
lean_object* v_inheritedTraceOptions_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_inheritedTraceOptions_448_ = lean_ctor_get(v___y_396_, 13);
v___x_449_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_450_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_451_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_448_, v_options_446_, v___x_450_);
if (v___x_451_ == 0)
{
v___y_404_ = v___y_388_;
goto v___jp_403_;
}
else
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Meta_Grind_updateLastTag(v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec_ref(v___x_452_);
v___x_453_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_400_);
v___x_454_ = l_Lean_MessageData_ofExpr(v_head_400_);
v___x_455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_449_, v___x_455_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_dec_ref(v___x_456_);
v___y_404_ = v___y_388_;
goto v___jp_403_;
}
else
{
return v___x_456_;
}
}
else
{
return v___x_452_;
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
lean_dec_ref(v___x_495_);
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
size_t v_x_28778__boxed_610_; lean_object* v_res_611_; 
v_x_28778__boxed_610_ = lean_unbox_usize(v_x_608_);
lean_dec(v_x_608_);
v_res_611_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_605_, v_00_u03b2_606_, v_x_607_, v_x_28778__boxed_610_, v_x_609_);
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
lean_object* v_head_629_; lean_object* v_tail_630_; lean_object* v___x_631_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; uint8_t v_a_646_; uint8_t v___x_659_; 
v_head_629_ = lean_ctor_get(v_as_x27_615_, 0);
v_tail_630_ = lean_ctor_get(v_as_x27_615_, 1);
v___x_631_ = lean_box(0);
v___x_659_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_629_);
if (v___x_659_ == 0)
{
v_a_646_ = v___x_659_;
goto v___jp_645_;
}
else
{
lean_object* v___x_660_; 
lean_inc(v_head_629_);
v___x_660_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_629_, v___y_617_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; uint8_t v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref(v___x_660_);
v___x_662_ = lean_unbox(v_a_661_);
lean_dec(v_a_661_);
v_a_646_ = v___x_662_;
goto v___jp_645_;
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
v_a_663_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_660_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_660_);
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
lean_dec_ref(v___x_643_);
v_as_x27_615_ = v_tail_630_;
v_b_616_ = v___x_631_;
goto _start;
}
else
{
return v___x_643_;
}
}
v___jp_645_:
{
if (v_a_646_ == 0)
{
v_as_x27_615_ = v_tail_630_;
v_b_616_ = v___x_631_;
goto _start;
}
else
{
lean_object* v_options_648_; uint8_t v_hasTrace_649_; 
v_options_648_ = lean_ctor_get(v___y_625_, 2);
v_hasTrace_649_ = lean_ctor_get_uint8(v_options_648_, sizeof(void*)*1);
if (v_hasTrace_649_ == 0)
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
lean_object* v_inheritedTraceOptions_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_inheritedTraceOptions_650_ = lean_ctor_get(v___y_625_, 13);
v___x_651_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_652_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_653_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_650_, v_options_648_, v___x_652_);
if (v___x_653_ == 0)
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
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Meta_Grind_updateLastTag(v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec_ref(v___x_654_);
v___x_655_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_629_);
v___x_656_ = l_Lean_MessageData_ofExpr(v_head_629_);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_651_, v___x_657_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_dec_ref(v___x_658_);
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
return v___x_658_;
}
}
else
{
return v___x_654_;
}
}
}
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
return v___x_759_;
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
lean_object* v_es_771_; lean_object* v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v_j_776_; lean_object* v___x_777_; 
v_es_771_ = lean_ctor_get(v_x_768_, 0);
v___x_772_ = lean_box(2);
v___x_773_ = ((size_t)5ULL);
v___x_774_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_775_ = lean_usize_land(v_x_769_, v___x_774_);
v_j_776_ = lean_usize_to_nat(v___x_775_);
v___x_777_ = lean_array_get_borrowed(v___x_772_, v_es_771_, v_j_776_);
lean_dec(v_j_776_);
switch(lean_obj_tag(v___x_777_))
{
case 0:
{
lean_object* v_key_778_; uint8_t v___x_779_; 
v_key_778_ = lean_ctor_get(v___x_777_, 0);
v___x_779_ = l_Lean_instBEqMVarId_beq(v_x_770_, v_key_778_);
return v___x_779_;
}
case 1:
{
lean_object* v_node_780_; size_t v___x_781_; 
v_node_780_ = lean_ctor_get(v___x_777_, 0);
v___x_781_ = lean_usize_shift_right(v_x_769_, v___x_773_);
v_x_768_ = v_node_780_;
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
size_t v_x_10242__boxed_790_; uint8_t v_res_791_; lean_object* v_r_792_; 
v_x_10242__boxed_790_ = lean_unbox_usize(v_x_788_);
lean_dec(v_x_788_);
v_res_791_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_787_, v_x_10242__boxed_790_, v_x_789_);
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
lean_dec_ref(v___x_853_);
v___x_855_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_854_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref(v___x_855_);
v___x_857_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_838_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref(v___x_857_);
v___x_859_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_838_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_859_);
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
size_t v_x_10527__boxed_958_; uint8_t v_res_959_; lean_object* v_r_960_; 
v_x_10527__boxed_958_ = lean_unbox_usize(v_x_956_);
lean_dec(v_x_956_);
v_res_959_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_954_, v_x_955_, v_x_10527__boxed_958_, v_x_957_);
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
lean_dec_ref(v___x_995_);
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
lean_dec_ref(v___x_997_);
lean_inc(v_a_996_);
v___x_999_ = l_Lean_Meta_mkDecide(v_a_996_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v___x_1001_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_988_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref(v___x_1001_);
v___x_1003_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1004_ = l_Lean_Expr_appArg_x21(v_a_1000_);
lean_dec(v_a_1000_);
v___x_1005_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_996_);
v___x_1006_ = l_Lean_mkApp3(v___x_1003_, v_a_996_, v___x_1004_, v___x_1005_);
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1008_ = l_Lean_mkApp4(v___x_1007_, v_a_996_, v_a_1002_, v___x_1006_, v_a_998_);
v___x_1009_ = l_Lean_Meta_Grind_closeGoal(v___x_1008_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_1009_;
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec(v_a_1000_);
lean_dec(v_a_998_);
lean_dec(v_a_996_);
v_a_1010_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1001_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1001_);
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
lean_object* v_head_1071_; lean_object* v_tail_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_head_1071_ = lean_ctor_get(v_as_x27_1057_, 0);
v_tail_1072_ = lean_ctor_get(v_as_x27_1057_, 1);
v___x_1073_ = lean_st_ref_get(v___y_1059_);
lean_inc(v_head_1071_);
v___x_1074_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1073_, v_head_1071_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___x_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v_self_1076_; lean_object* v_next_1077_; lean_object* v_root_1078_; lean_object* v_congr_1079_; lean_object* v_target_x3f_1080_; lean_object* v_proof_x3f_1081_; uint8_t v_flipped_1082_; lean_object* v_size_1083_; uint8_t v_interpreted_1084_; uint8_t v_ctor_1085_; uint8_t v_hasLambdas_1086_; uint8_t v_heqProofs_1087_; lean_object* v_idx_1088_; lean_object* v_generation_1089_; lean_object* v_mt_1090_; lean_object* v_sTerms_1091_; uint8_t v_funCC_1092_; lean_object* v_ematchDiagSource_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1106_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref(v___x_1074_);
v_self_1076_ = lean_ctor_get(v_a_1075_, 0);
v_next_1077_ = lean_ctor_get(v_a_1075_, 1);
v_root_1078_ = lean_ctor_get(v_a_1075_, 2);
v_congr_1079_ = lean_ctor_get(v_a_1075_, 3);
v_target_x3f_1080_ = lean_ctor_get(v_a_1075_, 4);
v_proof_x3f_1081_ = lean_ctor_get(v_a_1075_, 5);
v_flipped_1082_ = lean_ctor_get_uint8(v_a_1075_, sizeof(void*)*12);
v_size_1083_ = lean_ctor_get(v_a_1075_, 6);
v_interpreted_1084_ = lean_ctor_get_uint8(v_a_1075_, sizeof(void*)*12 + 1);
v_ctor_1085_ = lean_ctor_get_uint8(v_a_1075_, sizeof(void*)*12 + 2);
v_hasLambdas_1086_ = lean_ctor_get_uint8(v_a_1075_, sizeof(void*)*12 + 3);
v_heqProofs_1087_ = lean_ctor_get_uint8(v_a_1075_, sizeof(void*)*12 + 4);
v_idx_1088_ = lean_ctor_get(v_a_1075_, 7);
v_generation_1089_ = lean_ctor_get(v_a_1075_, 8);
v_mt_1090_ = lean_ctor_get(v_a_1075_, 9);
v_sTerms_1091_ = lean_ctor_get(v_a_1075_, 10);
v_funCC_1092_ = lean_ctor_get_uint8(v_a_1075_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1093_ = lean_ctor_get(v_a_1075_, 11);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_a_1075_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1095_ = v_a_1075_;
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_ematchDiagSource_1093_);
lean_inc(v_sTerms_1091_);
lean_inc(v_mt_1090_);
lean_inc(v_generation_1089_);
lean_inc(v_idx_1088_);
lean_inc(v_size_1083_);
lean_inc(v_proof_x3f_1081_);
lean_inc(v_target_x3f_1080_);
lean_inc(v_congr_1079_);
lean_inc(v_root_1078_);
lean_inc(v_next_1077_);
lean_inc(v_self_1076_);
lean_dec(v_a_1075_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_nat_dec_lt(v_mt_1090_, v___x_1056_);
lean_dec(v_mt_1090_);
if (v___x_1098_ == 0)
{
lean_del_object(v___x_1095_);
lean_dec(v_ematchDiagSource_1093_);
lean_dec(v_sTerms_1091_);
lean_dec(v_generation_1089_);
lean_dec(v_idx_1088_);
lean_dec(v_size_1083_);
lean_dec(v_proof_x3f_1081_);
lean_dec(v_target_x3f_1080_);
lean_dec_ref(v_congr_1079_);
lean_dec_ref(v_root_1078_);
lean_dec_ref(v_next_1077_);
lean_dec_ref(v_self_1076_);
v_as_x27_1057_ = v_tail_1072_;
v_b_1058_ = v___x_1097_;
goto _start;
}
else
{
lean_object* v___x_1101_; 
lean_inc(v___x_1056_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 9, v___x_1056_);
v___x_1101_ = v___x_1095_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_self_1076_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_next_1077_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_root_1078_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_congr_1079_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_target_x3f_1080_);
lean_ctor_set(v_reuseFailAlloc_1105_, 5, v_proof_x3f_1081_);
lean_ctor_set(v_reuseFailAlloc_1105_, 6, v_size_1083_);
lean_ctor_set(v_reuseFailAlloc_1105_, 7, v_idx_1088_);
lean_ctor_set(v_reuseFailAlloc_1105_, 8, v_generation_1089_);
lean_ctor_set(v_reuseFailAlloc_1105_, 9, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1105_, 10, v_sTerms_1091_);
lean_ctor_set(v_reuseFailAlloc_1105_, 11, v_ematchDiagSource_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12, v_flipped_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12 + 1, v_interpreted_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12 + 2, v_ctor_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12 + 3, v_hasLambdas_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12 + 4, v_heqProofs_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*12 + 5, v_funCC_1092_);
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
lean_dec_ref(v___x_1102_);
v___x_1103_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1071_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_dec_ref(v___x_1103_);
v_as_x27_1057_ = v_tail_1072_;
v_b_1058_ = v___x_1097_;
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
v_a_1107_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1074_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1074_);
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
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_st_ref_get(v_a_1116_);
v___x_1128_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_toGoalState_1129_; lean_object* v_ematch_1130_; lean_object* v_a_1131_; lean_object* v_gmt_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_toGoalState_1129_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_toGoalState_1129_);
lean_dec(v___x_1127_);
v_ematch_1130_ = lean_ctor_get(v_toGoalState_1129_, 12);
lean_inc_ref(v_ematch_1130_);
lean_dec_ref(v_toGoalState_1129_);
v_a_1131_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1131_);
lean_dec_ref(v___x_1128_);
v_gmt_1132_ = lean_ctor_get(v_ematch_1130_, 1);
lean_inc(v_gmt_1132_);
lean_dec_ref(v_ematch_1130_);
v___x_1133_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1131_);
lean_dec(v_a_1131_);
v___x_1134_ = lean_box(0);
v___x_1135_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1132_, v___x_1133_, v___x_1134_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
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
lean_dec(v___x_1127_);
v_a_1144_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1128_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1128_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_fst_1231_, lean_object* v_lams_1232_, lean_object* v_____r_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1228_, v_a_1229_, v___y_1234_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; uint8_t v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = lean_unbox(v_a_1293_);
lean_dec(v_a_1293_);
if (v___x_1294_ == 0)
{
v___y_1246_ = v___y_1234_;
v___y_1247_ = v___y_1235_;
v___y_1248_ = v___y_1236_;
v___y_1249_ = v___y_1237_;
v___y_1250_ = v___y_1238_;
v___y_1251_ = v___y_1239_;
v___y_1252_ = v___y_1240_;
v___y_1253_ = v___y_1241_;
v___y_1254_ = v___y_1242_;
v___y_1255_ = v___y_1243_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_inc(v_fst_1231_);
v___x_1295_ = l_Array_reverse___redArg(v_fst_1231_);
lean_inc(v_snd_1228_);
v___x_1296_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1232_, v_snd_1228_, v___x_1295_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_dec_ref(v___x_1296_);
v___y_1246_ = v___y_1234_;
v___y_1247_ = v___y_1235_;
v___y_1248_ = v___y_1236_;
v___y_1249_ = v___y_1237_;
v___y_1250_ = v___y_1238_;
v___y_1251_ = v___y_1239_;
v___y_1252_ = v___y_1240_;
v___y_1253_ = v___y_1241_;
v___y_1254_ = v___y_1242_;
v___y_1255_ = v___y_1243_;
goto v___jp_1245_;
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_fst_1231_);
lean_dec(v_snd_1228_);
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_fst_1231_);
lean_dec(v_snd_1228_);
v_a_1305_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1292_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1292_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
v___jp_1245_:
{
if (lean_obj_tag(v_snd_1228_) == 5)
{
lean_object* v_fn_1256_; lean_object* v_arg_1257_; lean_object* v___x_1258_; 
v_fn_1256_ = lean_ctor_get(v_snd_1228_, 0);
lean_inc_ref(v_fn_1256_);
v_arg_1257_ = lean_ctor_get(v_snd_1228_, 1);
lean_inc_ref(v_arg_1257_);
v___x_1258_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1230_, v___y_1246_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
v___x_1260_ = lean_box(0);
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
lean_inc(v___y_1251_);
lean_inc_ref(v___y_1250_);
lean_inc(v___y_1249_);
lean_inc_ref(v___y_1248_);
lean_inc(v___y_1247_);
lean_inc(v___y_1246_);
v___x_1261_ = lean_grind_internalize(v_snd_1228_, v_a_1259_, v___x_1260_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1271_; 
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v___x_1261_, 0);
lean_dec(v_unused_1272_);
v___x_1263_ = v___x_1261_;
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v___x_1261_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1271_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1265_ = lean_array_push(v_fst_1231_, v_arg_1257_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v_fn_1256_);
v___x_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1267_);
v___x_1269_ = v___x_1263_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v_arg_1257_);
lean_dec_ref(v_fn_1256_);
lean_dec(v_fst_1231_);
v_a_1273_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1261_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1261_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_arg_1257_);
lean_dec_ref(v_snd_1228_);
lean_dec_ref(v_fn_1256_);
lean_dec(v_fst_1231_);
v_a_1281_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1258_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1258_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v_fst_1231_);
lean_ctor_set(v___x_1289_, 1, v_snd_1228_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
return v___x_1291_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1313_ = _args[0];
lean_object* v_a_1314_ = _args[1];
lean_object* v_a_1315_ = _args[2];
lean_object* v_fst_1316_ = _args[3];
lean_object* v_lams_1317_ = _args[4];
lean_object* v_____r_1318_ = _args[5];
lean_object* v___y_1319_ = _args[6];
lean_object* v___y_1320_ = _args[7];
lean_object* v___y_1321_ = _args[8];
lean_object* v___y_1322_ = _args[9];
lean_object* v___y_1323_ = _args[10];
lean_object* v___y_1324_ = _args[11];
lean_object* v___y_1325_ = _args[12];
lean_object* v___y_1326_ = _args[13];
lean_object* v___y_1327_ = _args[14];
lean_object* v___y_1328_ = _args[15];
lean_object* v___y_1329_ = _args[16];
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1313_, v_a_1314_, v_a_1315_, v_fst_1316_, v_lams_1317_, v_____r_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v_lams_1317_);
lean_dec_ref(v_a_1315_);
lean_dec_ref(v_a_1314_);
return v_res_1330_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1337_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1338_ = l_Lean_Name_append(v___x_1337_, v___x_1336_);
return v___x_1338_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1341_ = l_Lean_stringToMessageData(v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_lams_1344_, lean_object* v_a_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___y_1358_; lean_object* v_options_1378_; lean_object* v_fst_1379_; lean_object* v_snd_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1417_; 
v_options_1378_ = lean_ctor_get(v___y_1354_, 2);
v_fst_1379_ = lean_ctor_get(v_a_1345_, 0);
v_snd_1380_ = lean_ctor_get(v_a_1345_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_a_1345_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1382_ = v_a_1345_;
v_isShared_1383_ = v_isSharedCheck_1417_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_snd_1380_);
lean_inc(v_fst_1379_);
lean_dec(v_a_1345_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1417_;
goto v_resetjp_1381_;
}
v___jp_1357_:
{
if (lean_obj_tag(v___y_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1369_; 
v_a_1359_ = lean_ctor_get(v___y_1358_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___y_1358_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1361_ = v___y_1358_;
v_isShared_1362_ = v_isSharedCheck_1369_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___y_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1369_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
if (lean_obj_tag(v_a_1359_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; 
v_a_1363_ = lean_ctor_get(v_a_1359_, 0);
lean_inc(v_a_1363_);
lean_dec_ref(v_a_1359_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v_a_1363_);
v___x_1365_ = v___x_1361_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
else
{
lean_object* v_a_1367_; 
lean_del_object(v___x_1361_);
v_a_1367_ = lean_ctor_get(v_a_1359_, 0);
lean_inc(v_a_1367_);
lean_dec_ref(v_a_1359_);
v_a_1345_ = v_a_1367_;
goto _start;
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1370_ = lean_ctor_get(v___y_1358_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___y_1358_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___y_1358_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___y_1358_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
v_resetjp_1381_:
{
lean_object* v_inheritedTraceOptions_1384_; uint8_t v_hasTrace_1385_; 
v_inheritedTraceOptions_1384_ = lean_ctor_get(v___y_1354_, 13);
v_hasTrace_1385_ = lean_ctor_get_uint8(v_options_1378_, sizeof(void*)*1);
if (v_hasTrace_1385_ == 0)
{
lean_del_object(v___x_1382_);
goto v___jp_1386_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1390_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1391_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1384_, v_options_1378_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_del_object(v___x_1382_);
goto v___jp_1386_;
}
else
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Meta_Grind_updateLastTag(v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_dec_ref(v___x_1392_);
v___x_1393_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1380_);
v___x_1394_ = l_Lean_MessageData_ofExpr(v_snd_1380_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 7);
lean_ctor_set(v___x_1382_, 1, v___x_1394_);
lean_ctor_set(v___x_1382_, 0, v___x_1393_);
v___x_1396_ = v___x_1382_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1389_, v___x_1396_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref(v___x_1397_);
v___x_1399_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1380_, v_a_1343_, v_a_1342_, v_fst_1379_, v_lams_1344_, v_a_1398_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v___y_1358_ = v___x_1399_;
goto v___jp_1357_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_snd_1380_);
lean_dec(v_fst_1379_);
v_a_1400_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1397_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1397_);
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
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_del_object(v___x_1382_);
lean_dec(v_snd_1380_);
lean_dec(v_fst_1379_);
v_a_1409_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1392_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1392_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
v___jp_1386_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1380_, v_a_1343_, v_a_1342_, v_fst_1379_, v_lams_1344_, v___x_1387_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v___y_1358_ = v___x_1388_;
goto v___jp_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_lams_1420_, lean_object* v_a_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1418_, v_a_1419_, v_lams_1420_, v_a_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v_lams_1420_);
lean_dec_ref(v_a_1419_);
lean_dec_ref(v_a_1418_);
return v_res_1433_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1438_ = l_Lean_stringToMessageData(v___x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1439_, lean_object* v_lams_1440_, lean_object* v_as_x27_1441_, lean_object* v_b_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
if (lean_obj_tag(v_as_x27_1441_) == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_b_1442_);
return v___x_1454_;
}
else
{
lean_object* v_options_1455_; lean_object* v_head_1456_; lean_object* v_tail_1457_; lean_object* v_inheritedTraceOptions_1458_; uint8_t v_hasTrace_1459_; lean_object* v___x_1460_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___x_1484_; uint8_t v_a_1486_; 
v_options_1455_ = lean_ctor_get(v___y_1451_, 2);
v_head_1456_ = lean_ctor_get(v_as_x27_1441_, 0);
v_tail_1457_ = lean_ctor_get(v_as_x27_1441_, 1);
v_inheritedTraceOptions_1458_ = lean_ctor_get(v___y_1451_, 13);
v_hasTrace_1459_ = lean_ctor_get_uint8(v_options_1455_, sizeof(void*)*1);
v___x_1460_ = lean_box(0);
v___x_1484_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
if (v_hasTrace_1459_ == 0)
{
v_a_1486_ = v_hasTrace_1459_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1493_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1494_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1458_, v_options_1455_, v___x_1493_);
v_a_1486_ = v___x_1494_;
goto v___jp_1485_;
}
v___jp_1461_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_inc(v_head_1456_);
lean_inc_ref(v___y_1462_);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___y_1462_);
lean_ctor_set(v___x_1473_, 1, v_head_1456_);
v___x_1474_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1456_, v_a_1439_, v_lams_1440_, v___x_1473_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_dec_ref(v___x_1474_);
v_as_x27_1441_ = v_tail_1457_;
v_b_1442_ = v___x_1460_;
goto _start;
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1474_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1474_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
v___jp_1485_:
{
lean_object* v___x_1487_; 
v___x_1487_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1486_ == 0)
{
v___y_1462_ = v___x_1487_;
v___y_1463_ = v___y_1443_;
v___y_1464_ = v___y_1444_;
v___y_1465_ = v___y_1445_;
v___y_1466_ = v___y_1446_;
v___y_1467_ = v___y_1447_;
v___y_1468_ = v___y_1448_;
v___y_1469_ = v___y_1449_;
v___y_1470_ = v___y_1450_;
v___y_1471_ = v___y_1451_;
v___y_1472_ = v___y_1452_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_Meta_Grind_updateLastTag(v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec_ref(v___x_1488_);
v___x_1489_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1456_);
v___x_1490_ = l_Lean_MessageData_ofExpr(v_head_1456_);
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1484_, v___x_1491_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_dec_ref(v___x_1492_);
v___y_1462_ = v___x_1487_;
v___y_1463_ = v___y_1443_;
v___y_1464_ = v___y_1444_;
v___y_1465_ = v___y_1445_;
v___y_1466_ = v___y_1446_;
v___y_1467_ = v___y_1447_;
v___y_1468_ = v___y_1448_;
v___y_1469_ = v___y_1449_;
v___y_1470_ = v___y_1450_;
v___y_1471_ = v___y_1451_;
v___y_1472_ = v___y_1452_;
goto v___jp_1461_;
}
else
{
return v___x_1492_;
}
}
else
{
return v___x_1488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1495_, lean_object* v_lams_1496_, lean_object* v_as_x27_1497_, lean_object* v_b_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1495_, v_lams_1496_, v_as_x27_1497_, v_b_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec(v_as_x27_1497_);
lean_dec_ref(v_lams_1496_);
lean_dec_ref(v_a_1495_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1511_, lean_object* v_lams_1512_, lean_object* v_as_1513_, lean_object* v_as_x27_1514_, lean_object* v_b_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
if (lean_obj_tag(v_as_x27_1514_) == 0)
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_b_1515_);
return v___x_1527_;
}
else
{
lean_object* v_options_1528_; lean_object* v_head_1529_; lean_object* v_tail_1530_; lean_object* v_inheritedTraceOptions_1531_; uint8_t v_hasTrace_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; uint8_t v_a_1559_; 
v_options_1528_ = lean_ctor_get(v___y_1524_, 2);
v_head_1529_ = lean_ctor_get(v_as_x27_1514_, 0);
v_tail_1530_ = lean_ctor_get(v_as_x27_1514_, 1);
v_inheritedTraceOptions_1531_ = lean_ctor_get(v___y_1524_, 13);
v_hasTrace_1532_ = lean_ctor_get_uint8(v_options_1528_, sizeof(void*)*1);
v___x_1533_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1534_ = lean_box(0);
if (v_hasTrace_1532_ == 0)
{
v_a_1559_ = v_hasTrace_1532_;
goto v___jp_1558_;
}
else
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1567_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1531_, v_options_1528_, v___x_1566_);
v_a_1559_ = v___x_1567_;
goto v___jp_1558_;
}
v___jp_1535_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_inc(v_head_1529_);
lean_inc_ref(v___y_1536_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___y_1536_);
lean_ctor_set(v___x_1547_, 1, v_head_1529_);
v___x_1548_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1529_, v_a_1511_, v_lams_1512_, v___x_1547_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v___x_1549_; 
lean_dec_ref(v___x_1548_);
v___x_1549_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1511_, v_lams_1512_, v_tail_1530_, v___x_1534_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
return v___x_1549_;
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1548_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1548_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
v___jp_1558_:
{
lean_object* v___x_1560_; 
v___x_1560_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1559_ == 0)
{
v___y_1536_ = v___x_1560_;
v___y_1537_ = v___y_1516_;
v___y_1538_ = v___y_1517_;
v___y_1539_ = v___y_1518_;
v___y_1540_ = v___y_1519_;
v___y_1541_ = v___y_1520_;
v___y_1542_ = v___y_1521_;
v___y_1543_ = v___y_1522_;
v___y_1544_ = v___y_1523_;
v___y_1545_ = v___y_1524_;
v___y_1546_ = v___y_1525_;
goto v___jp_1535_;
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Meta_Grind_updateLastTag(v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec_ref(v___x_1561_);
v___x_1562_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1529_);
v___x_1563_ = l_Lean_MessageData_ofExpr(v_head_1529_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1533_, v___x_1564_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_dec_ref(v___x_1565_);
v___y_1536_ = v___x_1560_;
v___y_1537_ = v___y_1516_;
v___y_1538_ = v___y_1517_;
v___y_1539_ = v___y_1518_;
v___y_1540_ = v___y_1519_;
v___y_1541_ = v___y_1520_;
v___y_1542_ = v___y_1521_;
v___y_1543_ = v___y_1522_;
v___y_1544_ = v___y_1523_;
v___y_1545_ = v___y_1524_;
v___y_1546_ = v___y_1525_;
goto v___jp_1535_;
}
else
{
return v___x_1565_;
}
}
else
{
return v___x_1561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1568_, lean_object* v_lams_1569_, lean_object* v_as_1570_, lean_object* v_as_x27_1571_, lean_object* v_b_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1568_, v_lams_1569_, v_as_1570_, v_as_x27_1571_, v_b_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec(v_as_x27_1571_);
lean_dec(v_as_1570_);
lean_dec_ref(v_lams_1569_);
lean_dec_ref(v_a_1568_);
return v_res_1584_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1587_ = l_Lean_stringToMessageData(v___x_1586_);
return v___x_1587_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1590_ = l_Lean_stringToMessageData(v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1591_, lean_object* v_lams_1592_, lean_object* v_as_1593_, size_t v_sz_1594_, size_t v_i_1595_, lean_object* v_b_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_usize_dec_lt(v_i_1595_, v_sz_1594_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_b_1596_);
return v___x_1609_;
}
else
{
lean_object* v_options_1610_; lean_object* v_inheritedTraceOptions_1611_; uint8_t v_hasTrace_1612_; lean_object* v___x_1613_; lean_object* v_a_1614_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; 
v_options_1610_ = lean_ctor_get(v___y_1605_, 2);
v_inheritedTraceOptions_1611_ = lean_ctor_get(v___y_1605_, 13);
v_hasTrace_1612_ = lean_ctor_get_uint8(v_options_1610_, sizeof(void*)*1);
v___x_1613_ = lean_box(0);
v_a_1614_ = lean_array_uget_borrowed(v_as_1593_, v_i_1595_);
if (v_hasTrace_1612_ == 0)
{
v___y_1616_ = v___y_1597_;
v___y_1617_ = v___y_1598_;
v___y_1618_ = v___y_1599_;
v___y_1619_ = v___y_1600_;
v___y_1620_ = v___y_1601_;
v___y_1621_ = v___y_1602_;
v___y_1622_ = v___y_1603_;
v___y_1623_ = v___y_1604_;
v___y_1624_ = v___y_1605_;
v___y_1625_ = v___y_1606_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1641_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1642_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1643_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1611_, v_options_1610_, v___x_1642_);
if (v___x_1643_ == 0)
{
v___y_1616_ = v___y_1597_;
v___y_1617_ = v___y_1598_;
v___y_1618_ = v___y_1599_;
v___y_1619_ = v___y_1600_;
v___y_1620_ = v___y_1601_;
v___y_1621_ = v___y_1602_;
v___y_1622_ = v___y_1603_;
v___y_1623_ = v___y_1604_;
v___y_1624_ = v___y_1605_;
v___y_1625_ = v___y_1606_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Meta_Grind_updateLastTag(v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v___x_1645_; 
lean_dec_ref(v___x_1644_);
v___x_1645_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1614_, v___y_1597_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1614_);
v___x_1648_ = l_Lean_MessageData_ofExpr(v_a_1614_);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1646_);
lean_dec(v_a_1646_);
v___x_1653_ = lean_box(0);
v___x_1654_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1652_, v___x_1653_);
v___x_1655_ = l_Lean_MessageData_ofList(v___x_1654_);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1651_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1641_, v___x_1656_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_dec_ref(v___x_1657_);
v___y_1616_ = v___y_1597_;
v___y_1617_ = v___y_1598_;
v___y_1618_ = v___y_1599_;
v___y_1619_ = v___y_1600_;
v___y_1620_ = v___y_1601_;
v___y_1621_ = v___y_1602_;
v___y_1622_ = v___y_1603_;
v___y_1623_ = v___y_1604_;
v___y_1624_ = v___y_1605_;
v___y_1625_ = v___y_1606_;
goto v___jp_1615_;
}
else
{
return v___x_1657_;
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
v_a_1658_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1645_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1645_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
return v___x_1644_;
}
}
}
v___jp_1615_:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1614_, v___y_1616_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1627_);
lean_dec(v_a_1627_);
v___x_1629_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1591_, v_lams_1592_, v___x_1628_, v___x_1628_, v___x_1613_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___x_1628_);
if (lean_obj_tag(v___x_1629_) == 0)
{
size_t v___x_1630_; size_t v___x_1631_; 
lean_dec_ref(v___x_1629_);
v___x_1630_ = ((size_t)1ULL);
v___x_1631_ = lean_usize_add(v_i_1595_, v___x_1630_);
v_i_1595_ = v___x_1631_;
v_b_1596_ = v___x_1613_;
goto _start;
}
else
{
return v___x_1629_;
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v_a_1633_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1626_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1626_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1666_ = _args[0];
lean_object* v_lams_1667_ = _args[1];
lean_object* v_as_1668_ = _args[2];
lean_object* v_sz_1669_ = _args[3];
lean_object* v_i_1670_ = _args[4];
lean_object* v_b_1671_ = _args[5];
lean_object* v___y_1672_ = _args[6];
lean_object* v___y_1673_ = _args[7];
lean_object* v___y_1674_ = _args[8];
lean_object* v___y_1675_ = _args[9];
lean_object* v___y_1676_ = _args[10];
lean_object* v___y_1677_ = _args[11];
lean_object* v___y_1678_ = _args[12];
lean_object* v___y_1679_ = _args[13];
lean_object* v___y_1680_ = _args[14];
lean_object* v___y_1681_ = _args[15];
lean_object* v___y_1682_ = _args[16];
_start:
{
size_t v_sz_boxed_1683_; size_t v_i_boxed_1684_; lean_object* v_res_1685_; 
v_sz_boxed_1683_ = lean_unbox_usize(v_sz_1669_);
lean_dec(v_sz_1669_);
v_i_boxed_1684_ = lean_unbox_usize(v_i_1670_);
lean_dec(v_i_1670_);
v_res_1685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1666_, v_lams_1667_, v_as_1668_, v_sz_boxed_1683_, v_i_boxed_1684_, v_b_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v_as_1668_);
lean_dec_ref(v_lams_1667_);
lean_dec_ref(v_a_1666_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1686_, lean_object* v_lams_1687_, lean_object* v_as_1688_, size_t v_sz_1689_, size_t v_i_1690_, lean_object* v_b_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_usize_dec_lt(v_i_1690_, v_sz_1689_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_b_1691_);
return v___x_1704_;
}
else
{
lean_object* v_options_1705_; lean_object* v_inheritedTraceOptions_1706_; uint8_t v_hasTrace_1707_; lean_object* v___x_1708_; lean_object* v_a_1709_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; 
v_options_1705_ = lean_ctor_get(v___y_1700_, 2);
v_inheritedTraceOptions_1706_ = lean_ctor_get(v___y_1700_, 13);
v_hasTrace_1707_ = lean_ctor_get_uint8(v_options_1705_, sizeof(void*)*1);
v___x_1708_ = lean_box(0);
v_a_1709_ = lean_array_uget_borrowed(v_as_1688_, v_i_1690_);
if (v_hasTrace_1707_ == 0)
{
v___y_1711_ = v___y_1692_;
v___y_1712_ = v___y_1693_;
v___y_1713_ = v___y_1694_;
v___y_1714_ = v___y_1695_;
v___y_1715_ = v___y_1696_;
v___y_1716_ = v___y_1697_;
v___y_1717_ = v___y_1698_;
v___y_1718_ = v___y_1699_;
v___y_1719_ = v___y_1700_;
v___y_1720_ = v___y_1701_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1736_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1737_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1738_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1706_, v_options_1705_, v___x_1737_);
if (v___x_1738_ == 0)
{
v___y_1711_ = v___y_1692_;
v___y_1712_ = v___y_1693_;
v___y_1713_ = v___y_1694_;
v___y_1714_ = v___y_1695_;
v___y_1715_ = v___y_1696_;
v___y_1716_ = v___y_1697_;
v___y_1717_ = v___y_1698_;
v___y_1718_ = v___y_1699_;
v___y_1719_ = v___y_1700_;
v___y_1720_ = v___y_1701_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Meta_Grind_updateLastTag(v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref(v___x_1739_);
v___x_1740_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1709_, v___y_1692_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1709_);
v___x_1743_ = l_Lean_MessageData_ofExpr(v_a_1709_);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1741_);
lean_dec(v_a_1741_);
v___x_1748_ = lean_box(0);
v___x_1749_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1747_, v___x_1748_);
v___x_1750_ = l_Lean_MessageData_ofList(v___x_1749_);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1746_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1736_, v___x_1751_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_dec_ref(v___x_1752_);
v___y_1711_ = v___y_1692_;
v___y_1712_ = v___y_1693_;
v___y_1713_ = v___y_1694_;
v___y_1714_ = v___y_1695_;
v___y_1715_ = v___y_1696_;
v___y_1716_ = v___y_1697_;
v___y_1717_ = v___y_1698_;
v___y_1718_ = v___y_1699_;
v___y_1719_ = v___y_1700_;
v___y_1720_ = v___y_1701_;
goto v___jp_1710_;
}
else
{
return v___x_1752_;
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
v_a_1753_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1740_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1740_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
return v___x_1739_;
}
}
}
v___jp_1710_:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1709_, v___y_1711_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref(v___x_1721_);
v___x_1723_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1722_);
lean_dec(v_a_1722_);
v___x_1724_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1686_, v_lams_1687_, v___x_1723_, v___x_1723_, v___x_1708_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___x_1723_);
if (lean_obj_tag(v___x_1724_) == 0)
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v___x_1724_);
v___x_1725_ = ((size_t)1ULL);
v___x_1726_ = lean_usize_add(v_i_1690_, v___x_1725_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1686_, v_lams_1687_, v_as_1688_, v_sz_1689_, v___x_1726_, v___x_1708_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1727_;
}
else
{
return v___x_1724_;
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
v_a_1728_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1721_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1721_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1761_ = _args[0];
lean_object* v_lams_1762_ = _args[1];
lean_object* v_as_1763_ = _args[2];
lean_object* v_sz_1764_ = _args[3];
lean_object* v_i_1765_ = _args[4];
lean_object* v_b_1766_ = _args[5];
lean_object* v___y_1767_ = _args[6];
lean_object* v___y_1768_ = _args[7];
lean_object* v___y_1769_ = _args[8];
lean_object* v___y_1770_ = _args[9];
lean_object* v___y_1771_ = _args[10];
lean_object* v___y_1772_ = _args[11];
lean_object* v___y_1773_ = _args[12];
lean_object* v___y_1774_ = _args[13];
lean_object* v___y_1775_ = _args[14];
lean_object* v___y_1776_ = _args[15];
lean_object* v___y_1777_ = _args[16];
_start:
{
size_t v_sz_boxed_1778_; size_t v_i_boxed_1779_; lean_object* v_res_1780_; 
v_sz_boxed_1778_ = lean_unbox_usize(v_sz_1764_);
lean_dec(v_sz_1764_);
v_i_boxed_1779_ = lean_unbox_usize(v_i_1765_);
lean_dec(v_i_1765_);
v_res_1780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1761_, v_lams_1762_, v_as_1763_, v_sz_boxed_1778_, v_i_boxed_1779_, v_b_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v_as_1763_);
lean_dec_ref(v_lams_1762_);
lean_dec_ref(v_a_1761_);
return v_res_1780_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1787_, lean_object* v_fns_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1800_ = lean_array_get_size(v_lams_1787_);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_nat_dec_eq(v___x_1800_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1803_ = lean_st_ref_get(v_a_1789_);
v___x_1804_ = l_Lean_instInhabitedExpr;
v___x_1805_ = lean_unsigned_to_nat(1u);
v___x_1806_ = lean_nat_sub(v___x_1800_, v___x_1805_);
v___x_1807_ = lean_array_get_borrowed(v___x_1804_, v_lams_1787_, v___x_1806_);
lean_dec(v___x_1806_);
lean_inc(v___x_1807_);
v___x_1808_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1803_, v___x_1807_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v___x_1803_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v_options_1833_; uint8_t v_hasTrace_1834_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref(v___x_1808_);
v_options_1833_ = lean_ctor_get(v_a_1797_, 2);
v_hasTrace_1834_ = lean_ctor_get_uint8(v_options_1833_, sizeof(void*)*1);
if (v_hasTrace_1834_ == 0)
{
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
v___y_1814_ = v_a_1792_;
v___y_1815_ = v_a_1793_;
v___y_1816_ = v_a_1794_;
v___y_1817_ = v_a_1795_;
v___y_1818_ = v_a_1796_;
v___y_1819_ = v_a_1797_;
v___y_1820_ = v_a_1798_;
goto v___jp_1810_;
}
else
{
lean_object* v_inheritedTraceOptions_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v_inheritedTraceOptions_1835_ = lean_ctor_get(v_a_1797_, 13);
v___x_1836_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1837_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1838_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1835_, v_options_1833_, v___x_1837_);
if (v___x_1838_ == 0)
{
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
v___y_1814_ = v_a_1792_;
v___y_1815_ = v_a_1793_;
v___y_1816_ = v_a_1794_;
v___y_1817_ = v_a_1795_;
v___y_1818_ = v_a_1796_;
v___y_1819_ = v_a_1797_;
v___y_1820_ = v_a_1798_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_Meta_Grind_updateLastTag(v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec_ref(v___x_1839_);
v___x_1840_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1788_);
v___x_1841_ = lean_array_to_list(v_fns_1788_);
v___x_1842_ = lean_box(0);
v___x_1843_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1841_, v___x_1842_);
v___x_1844_ = l_Lean_MessageData_ofList(v___x_1843_);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1840_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
lean_inc_ref(v_lams_1787_);
v___x_1848_ = lean_array_to_list(v_lams_1787_);
v___x_1849_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1848_, v___x_1842_);
v___x_1850_ = l_Lean_MessageData_ofList(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1847_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1836_, v___x_1851_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_dec_ref(v___x_1852_);
v___y_1811_ = v_a_1789_;
v___y_1812_ = v_a_1790_;
v___y_1813_ = v_a_1791_;
v___y_1814_ = v_a_1792_;
v___y_1815_ = v_a_1793_;
v___y_1816_ = v_a_1794_;
v___y_1817_ = v_a_1795_;
v___y_1818_ = v_a_1796_;
v___y_1819_ = v_a_1797_;
v___y_1820_ = v_a_1798_;
goto v___jp_1810_;
}
else
{
lean_dec(v_a_1809_);
lean_dec_ref(v_fns_1788_);
lean_dec_ref(v_lams_1787_);
return v___x_1852_;
}
}
else
{
lean_dec(v_a_1809_);
lean_dec_ref(v_fns_1788_);
lean_dec_ref(v_lams_1787_);
return v___x_1839_;
}
}
}
v___jp_1810_:
{
lean_object* v___x_1821_; size_t v_sz_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1821_ = lean_box(0);
v_sz_1822_ = lean_array_size(v_fns_1788_);
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1809_, v_lams_1787_, v_fns_1788_, v_sz_1822_, v___x_1823_, v___x_1821_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec_ref(v_fns_1788_);
lean_dec_ref(v_lams_1787_);
lean_dec(v_a_1809_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; 
v_unused_1832_ = lean_ctor_get(v___x_1824_, 0);
lean_dec(v_unused_1832_);
v___x_1826_ = v___x_1824_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_dec(v___x_1824_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1821_);
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1821_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
else
{
return v___x_1824_;
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v_fns_1788_);
lean_dec_ref(v_lams_1787_);
v_a_1853_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1808_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1808_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_dec_ref(v_fns_1788_);
lean_dec_ref(v_lams_1787_);
v___x_1861_ = lean_box(0);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1863_, lean_object* v_fns_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1863_, v_fns_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec(v_a_1865_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_lams_1879_, lean_object* v_inst_1880_, lean_object* v_a_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1877_, v_a_1878_, v_lams_1879_, v_a_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_lams_1896_, lean_object* v_inst_1897_, lean_object* v_a_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1894_, v_a_1895_, v_lams_1896_, v_inst_1897_, v_a_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v_lams_1896_);
lean_dec_ref(v_a_1895_);
lean_dec_ref(v_a_1894_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1911_, lean_object* v_lams_1912_, lean_object* v_as_1913_, lean_object* v_as_x27_1914_, lean_object* v_b_1915_, lean_object* v_a_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1911_, v_lams_1912_, v_as_1913_, v_as_x27_1914_, v_b_1915_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1929_ = _args[0];
lean_object* v_lams_1930_ = _args[1];
lean_object* v_as_1931_ = _args[2];
lean_object* v_as_x27_1932_ = _args[3];
lean_object* v_b_1933_ = _args[4];
lean_object* v_a_1934_ = _args[5];
lean_object* v___y_1935_ = _args[6];
lean_object* v___y_1936_ = _args[7];
lean_object* v___y_1937_ = _args[8];
lean_object* v___y_1938_ = _args[9];
lean_object* v___y_1939_ = _args[10];
lean_object* v___y_1940_ = _args[11];
lean_object* v___y_1941_ = _args[12];
lean_object* v___y_1942_ = _args[13];
lean_object* v___y_1943_ = _args[14];
lean_object* v___y_1944_ = _args[15];
lean_object* v___y_1945_ = _args[16];
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1929_, v_lams_1930_, v_as_1931_, v_as_x27_1932_, v_b_1933_, v_a_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec(v_as_x27_1932_);
lean_dec(v_as_1931_);
lean_dec_ref(v_lams_1930_);
lean_dec_ref(v_a_1929_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1947_, lean_object* v_lams_1948_, lean_object* v_as_1949_, lean_object* v_as_x27_1950_, lean_object* v_b_1951_, lean_object* v_a_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1947_, v_lams_1948_, v_as_x27_1950_, v_b_1951_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1965_ = _args[0];
lean_object* v_lams_1966_ = _args[1];
lean_object* v_as_1967_ = _args[2];
lean_object* v_as_x27_1968_ = _args[3];
lean_object* v_b_1969_ = _args[4];
lean_object* v_a_1970_ = _args[5];
lean_object* v___y_1971_ = _args[6];
lean_object* v___y_1972_ = _args[7];
lean_object* v___y_1973_ = _args[8];
lean_object* v___y_1974_ = _args[9];
lean_object* v___y_1975_ = _args[10];
lean_object* v___y_1976_ = _args[11];
lean_object* v___y_1977_ = _args[12];
lean_object* v___y_1978_ = _args[13];
lean_object* v___y_1979_ = _args[14];
lean_object* v___y_1980_ = _args[15];
lean_object* v___y_1981_ = _args[16];
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1965_, v_lams_1966_, v_as_1967_, v_as_x27_1968_, v_b_1969_, v_a_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec(v_as_x27_1968_);
lean_dec(v_as_1967_);
lean_dec_ref(v_lams_1966_);
lean_dec_ref(v_a_1965_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1986_, lean_object* v_as_1987_, size_t v_sz_1988_, size_t v_i_1989_, lean_object* v_b_1990_){
_start:
{
lean_object* v_a_1992_; uint8_t v___x_1996_; 
v___x_1996_ = lean_usize_dec_lt(v_i_1989_, v_sz_1988_);
if (v___x_1996_ == 0)
{
lean_inc_ref(v_b_1990_);
return v_b_1990_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v_a_1999_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1999_ = lean_array_uget_borrowed(v_as_1987_, v_i_1989_);
if (lean_obj_tag(v_a_1999_) == 6)
{
lean_object* v_binderType_2000_; uint8_t v___x_2001_; 
v_binderType_2000_ = lean_ctor_get(v_a_1999_, 1);
v___x_2001_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_d_1986_, v_binderType_2000_);
if (v___x_2001_ == 0)
{
v_a_1992_ = v___x_1998_;
goto v___jp_1991_;
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
lean_inc_ref(v_a_1999_);
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v_a_1999_);
v___x_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v___x_1997_);
return v___x_2004_;
}
}
else
{
v_a_1992_ = v___x_1998_;
goto v___jp_1991_;
}
}
v___jp_1991_:
{
size_t v___x_1993_; size_t v___x_1994_; 
v___x_1993_ = ((size_t)1ULL);
v___x_1994_ = lean_usize_add(v_i_1989_, v___x_1993_);
v_i_1989_ = v___x_1994_;
v_b_1990_ = v_a_1992_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_2005_, lean_object* v_as_2006_, lean_object* v_sz_2007_, lean_object* v_i_2008_, lean_object* v_b_2009_){
_start:
{
size_t v_sz_boxed_2010_; size_t v_i_boxed_2011_; lean_object* v_res_2012_; 
v_sz_boxed_2010_ = lean_unbox_usize(v_sz_2007_);
lean_dec(v_sz_2007_);
v_i_boxed_2011_ = lean_unbox_usize(v_i_2008_);
lean_dec(v_i_2008_);
v_res_2012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2005_, v_as_2006_, v_sz_boxed_2010_, v_i_boxed_2011_, v_b_2009_);
lean_dec_ref(v_b_2009_);
lean_dec_ref(v_as_2006_);
lean_dec_ref(v_d_2005_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2013_, lean_object* v_d_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; size_t v_sz_2017_; size_t v___x_2018_; lean_object* v___x_2019_; lean_object* v_fst_2020_; 
v___x_2015_ = lean_box(0);
v___x_2016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2017_ = lean_array_size(v_lams_2013_);
v___x_2018_ = ((size_t)0ULL);
v___x_2019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2014_, v_lams_2013_, v_sz_2017_, v___x_2018_, v___x_2016_);
v_fst_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_fst_2020_);
lean_dec_ref(v___x_2019_);
if (lean_obj_tag(v_fst_2020_) == 0)
{
return v___x_2015_;
}
else
{
lean_object* v_val_2021_; 
v_val_2021_ = lean_ctor_get(v_fst_2020_, 0);
lean_inc(v_val_2021_);
lean_dec_ref(v_fst_2020_);
return v_val_2021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2022_, lean_object* v_d_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2022_, v_d_2023_);
lean_dec_ref(v_d_2023_);
lean_dec_ref(v_lams_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2035_, lean_object* v_lams_u2081_2036_, lean_object* v_as_2037_, size_t v_sz_2038_, size_t v_i_2039_, lean_object* v_b_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_a_2053_; uint8_t v___x_2057_; 
v___x_2057_ = lean_usize_dec_lt(v_i_2039_, v_sz_2038_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v_b_2040_);
return v___x_2058_;
}
else
{
lean_object* v___x_2059_; lean_object* v_a_2060_; 
v___x_2059_ = lean_box(0);
v_a_2060_ = lean_array_uget_borrowed(v_as_2037_, v_i_2039_);
if (lean_obj_tag(v_a_2060_) == 6)
{
lean_object* v_binderType_2061_; lean_object* v_body_2062_; lean_object* v___x_2063_; 
v_binderType_2061_ = lean_ctor_get(v_a_2060_, 1);
v_body_2062_ = lean_ctor_get(v_a_2060_, 2);
lean_inc_ref(v_binderType_2061_);
v___x_2063_ = l_Lean_Meta_getLevel(v_binderType_2061_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
v___x_2065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2066_ = lean_box(0);
v___x_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2067_, 0, v_a_2064_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
lean_inc_ref(v___x_2067_);
v___x_2068_ = l_Lean_mkConst(v___x_2065_, v___x_2067_);
lean_inc_ref(v_binderType_2061_);
v___x_2069_ = l_Lean_Expr_app___override(v___x_2068_, v_binderType_2061_);
v___x_2070_ = lean_box(0);
v___x_2071_ = l_Lean_Meta_synthInstance_x3f(v___x_2069_, v___x_2070_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
if (lean_obj_tag(v_a_2072_) == 1)
{
lean_object* v_val_2073_; lean_object* v___x_2074_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; uint8_t v___x_2139_; 
v_val_2073_ = lean_ctor_get(v_a_2072_, 0);
lean_inc(v_val_2073_);
lean_dec_ref(v_a_2072_);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2139_ = l_Lean_Expr_hasLooseBVars(v_body_2062_);
if (v___x_2139_ == 0)
{
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
v___y_2081_ = v___y_2046_;
v___y_2082_ = v___y_2047_;
v___y_2083_ = v___y_2048_;
v___y_2084_ = v___y_2049_;
v___y_2085_ = v___y_2050_;
goto v___jp_2075_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2067_);
v___x_2141_ = l_Lean_mkConst(v___x_2140_, v___x_2067_);
lean_inc_ref(v_binderType_2061_);
v___x_2142_ = l_Lean_Expr_app___override(v___x_2141_, v_binderType_2061_);
v___x_2143_ = l_Lean_Meta_synthInstance_x3f(v___x_2142_, v___x_2070_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref(v___x_2143_);
if (lean_obj_tag(v_a_2144_) == 0)
{
lean_dec(v_val_2073_);
lean_dec_ref(v___x_2067_);
v_a_2053_ = v___x_2059_;
goto v___jp_2052_;
}
else
{
lean_dec_ref(v_a_2144_);
if (v___x_2139_ == 0)
{
lean_dec(v_val_2073_);
lean_dec_ref(v___x_2067_);
v_a_2053_ = v___x_2059_;
goto v___jp_2052_;
}
else
{
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
v___y_2081_ = v___y_2046_;
v___y_2082_ = v___y_2047_;
v___y_2083_ = v___y_2048_;
v___y_2084_ = v___y_2049_;
v___y_2085_ = v___y_2050_;
goto v___jp_2075_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_val_2073_);
lean_dec_ref(v___x_2067_);
v_a_2145_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2143_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2143_);
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
v___jp_2075_:
{
lean_object* v___x_2086_; 
v___x_2086_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2035_, v_binderType_2061_);
if (lean_obj_tag(v___x_2086_) == 1)
{
lean_object* v_val_2087_; 
v_val_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_val_2087_);
lean_dec_ref(v___x_2086_);
if (lean_obj_tag(v_val_2087_) == 6)
{
lean_object* v_binderType_2088_; lean_object* v_body_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v_binderType_2088_ = lean_ctor_get(v_val_2087_, 1);
lean_inc_ref(v_binderType_2088_);
v_body_2089_ = lean_ctor_get(v_val_2087_, 2);
lean_inc_ref(v_body_2089_);
lean_dec_ref(v_val_2087_);
v___x_2090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2091_ = l_Lean_mkConst(v___x_2090_, v___x_2067_);
v___x_2092_ = l_Lean_mkAppB(v___x_2091_, v_binderType_2088_, v_val_2073_);
v___x_2093_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2092_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref(v___x_2093_);
v___x_2095_ = lean_array_fget_borrowed(v_lams_u2081_2036_, v___x_2074_);
v___x_2096_ = lean_array_fget_borrowed(v_lams_u2082_2035_, v___x_2074_);
lean_inc(v___y_2085_);
lean_inc_ref(v___y_2084_);
lean_inc(v___y_2083_);
lean_inc_ref(v___y_2082_);
lean_inc(v___y_2081_);
lean_inc_ref(v___y_2080_);
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2078_);
lean_inc(v___y_2077_);
lean_inc(v___y_2076_);
lean_inc(v___x_2096_);
lean_inc(v___x_2095_);
v___x_2097_ = lean_grind_mk_eq_proof(v___x_2095_, v___x_2096_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref(v___x_2097_);
v___x_2099_ = lean_expr_instantiate1(v_body_2062_, v_a_2094_);
v___x_2100_ = lean_expr_instantiate1(v_body_2089_, v_a_2094_);
lean_dec_ref(v_body_2089_);
v___x_2101_ = l_Lean_Meta_mkCongrFun(v_a_2098_, v_a_2094_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2101_);
v___x_2103_ = l_Lean_Meta_mkEq(v___x_2099_, v___x_2100_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2103_);
v___x_2105_ = l_Lean_Meta_mkExpectedPropHint(v_a_2102_, v_a_2104_);
v___x_2106_ = l_Lean_Meta_Grind_pushNewFact(v___x_2105_, v___x_2074_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_dec_ref(v___x_2106_);
v_a_2053_ = v___x_2059_;
goto v___jp_2052_;
}
else
{
return v___x_2106_;
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v_a_2102_);
v_a_2107_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2103_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2103_);
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
lean_dec_ref(v___x_2100_);
lean_dec_ref(v___x_2099_);
v_a_2115_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2101_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2101_);
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
lean_dec(v_a_2094_);
lean_dec_ref(v_body_2089_);
v_a_2123_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2097_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2097_);
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
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref(v_body_2089_);
v_a_2131_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2093_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2093_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_dec(v_val_2087_);
lean_dec(v_val_2073_);
lean_dec_ref(v___x_2067_);
v_a_2053_ = v___x_2059_;
goto v___jp_2052_;
}
}
else
{
lean_dec(v___x_2086_);
lean_dec(v_val_2073_);
lean_dec_ref(v___x_2067_);
v_a_2053_ = v___x_2059_;
goto v___jp_2052_;
}
}
}
else
{
lean_dec(v_a_2072_);
lean_dec_ref(v___x_2067_);
v_a_2053_ = v___x_2059_;
goto v___jp_2052_;
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v___x_2067_);
v_a_2153_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2071_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2071_);
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
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
v_a_2161_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2063_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2063_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
v_a_2053_ = v___x_2059_;
goto v___jp_2052_;
}
}
v___jp_2052_:
{
size_t v___x_2054_; size_t v___x_2055_; 
v___x_2054_ = ((size_t)1ULL);
v___x_2055_ = lean_usize_add(v_i_2039_, v___x_2054_);
v_i_2039_ = v___x_2055_;
v_b_2040_ = v_a_2053_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2169_ = _args[0];
lean_object* v_lams_u2081_2170_ = _args[1];
lean_object* v_as_2171_ = _args[2];
lean_object* v_sz_2172_ = _args[3];
lean_object* v_i_2173_ = _args[4];
lean_object* v_b_2174_ = _args[5];
lean_object* v___y_2175_ = _args[6];
lean_object* v___y_2176_ = _args[7];
lean_object* v___y_2177_ = _args[8];
lean_object* v___y_2178_ = _args[9];
lean_object* v___y_2179_ = _args[10];
lean_object* v___y_2180_ = _args[11];
lean_object* v___y_2181_ = _args[12];
lean_object* v___y_2182_ = _args[13];
lean_object* v___y_2183_ = _args[14];
lean_object* v___y_2184_ = _args[15];
lean_object* v___y_2185_ = _args[16];
_start:
{
size_t v_sz_boxed_2186_; size_t v_i_boxed_2187_; lean_object* v_res_2188_; 
v_sz_boxed_2186_ = lean_unbox_usize(v_sz_2172_);
lean_dec(v_sz_2172_);
v_i_boxed_2187_ = lean_unbox_usize(v_i_2173_);
lean_dec(v_i_2173_);
v_res_2188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2169_, v_lams_u2081_2170_, v_as_2171_, v_sz_boxed_2186_, v_i_boxed_2187_, v_b_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v_as_2171_);
lean_dec_ref(v_lams_u2081_2170_);
lean_dec_ref(v_lams_u2082_2169_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2189_, lean_object* v_lams_u2082_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2202_ = lean_array_get_size(v_lams_u2081_2189_);
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = lean_nat_dec_eq(v___x_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = lean_array_get_size(v_lams_u2082_2190_);
v___x_2206_ = lean_nat_dec_eq(v___x_2205_, v___x_2203_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; size_t v_sz_2208_; size_t v___x_2209_; lean_object* v___x_2210_; 
v___x_2207_ = lean_box(0);
v_sz_2208_ = lean_array_size(v_lams_u2081_2189_);
v___x_2209_ = ((size_t)0ULL);
v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2190_, v_lams_u2081_2189_, v_lams_u2081_2189_, v_sz_2208_, v___x_2209_, v___x_2207_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; 
v_unused_2218_ = lean_ctor_get(v___x_2210_, 0);
lean_dec(v_unused_2218_);
v___x_2212_ = v___x_2210_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_dec(v___x_2210_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2207_);
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2207_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
else
{
return v___x_2210_;
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2223_, lean_object* v_lams_u2082_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2223_, v_lams_u2082_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_lams_u2082_2224_);
lean_dec_ref(v_lams_u2081_2223_);
return v_res_2236_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2237_){
_start:
{
uint8_t v___x_2238_; 
v___x_2238_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2239_){
_start:
{
uint8_t v_res_2240_; lean_object* v_r_2241_; 
v_res_2240_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2239_);
lean_dec_ref(v_x_2239_);
v_r_2241_ = lean_box(v_res_2240_);
return v_r_2241_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2242_, lean_object* v_x_2243_){
_start:
{
uint8_t v___x_2244_; 
v___x_2244_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2245_, lean_object* v_x_2246_){
_start:
{
uint8_t v_res_2247_; lean_object* v_r_2248_; 
v_res_2247_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2245_, v_x_2246_);
lean_dec_ref(v_x_2246_);
v_r_2248_ = lean_box(v_res_2247_);
return v_r_2248_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2249_, lean_object* v_v_2250_, lean_object* v_i_2251_){
_start:
{
lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = lean_array_get_size(v_xs_2249_);
v___x_2253_ = lean_nat_dec_lt(v_i_2251_, v___x_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
lean_dec(v_i_2251_);
v___x_2254_ = lean_box(0);
return v___x_2254_;
}
else
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = lean_array_fget_borrowed(v_xs_2249_, v_i_2251_);
v___x_2256_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2255_, v_v_2250_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2258_ = lean_nat_add(v_i_2251_, v___x_2257_);
lean_dec(v_i_2251_);
v_i_2251_ = v___x_2258_;
goto _start;
}
else
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2260_, 0, v_i_2251_);
return v___x_2260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2261_, lean_object* v_v_2262_, lean_object* v_i_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2261_, v_v_2262_, v_i_2263_);
lean_dec_ref(v_v_2262_);
lean_dec_ref(v_xs_2261_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2265_, lean_object* v_v_2266_){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2265_, v_v_2266_, v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2269_, lean_object* v_v_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2269_, v_v_2270_);
lean_dec_ref(v_v_2270_);
lean_dec_ref(v_xs_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2272_, size_t v_x_2273_, lean_object* v_x_2274_){
_start:
{
if (lean_obj_tag(v_x_2272_) == 0)
{
lean_object* v_es_2275_; lean_object* v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; size_t v___x_2279_; lean_object* v_j_2280_; lean_object* v_entry_2281_; 
v_es_2275_ = lean_ctor_get(v_x_2272_, 0);
v___x_2276_ = lean_box(2);
v___x_2277_ = ((size_t)5ULL);
v___x_2278_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2279_ = lean_usize_land(v_x_2273_, v___x_2278_);
v_j_2280_ = lean_usize_to_nat(v___x_2279_);
v_entry_2281_ = lean_array_get(v___x_2276_, v_es_2275_, v_j_2280_);
switch(lean_obj_tag(v_entry_2281_))
{
case 0:
{
lean_object* v_key_2282_; uint8_t v___x_2283_; 
v_key_2282_ = lean_ctor_get(v_entry_2281_, 0);
lean_inc(v_key_2282_);
lean_dec_ref(v_entry_2281_);
v___x_2283_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2274_, v_key_2282_);
lean_dec(v_key_2282_);
if (v___x_2283_ == 0)
{
lean_dec(v_j_2280_);
return v_x_2272_;
}
else
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2291_; 
lean_inc_ref(v_es_2275_);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_x_2272_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v_x_2272_, 0);
lean_dec(v_unused_2292_);
v___x_2285_ = v_x_2272_;
v_isShared_2286_ = v_isSharedCheck_2291_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v_x_2272_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2291_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = lean_array_set(v_es_2275_, v_j_2280_, v___x_2276_);
lean_dec(v_j_2280_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2287_);
v___x_2289_ = v___x_2285_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
case 1:
{
lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2326_; 
lean_inc_ref(v_es_2275_);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_x_2272_);
if (v_isSharedCheck_2326_ == 0)
{
lean_object* v_unused_2327_; 
v_unused_2327_ = lean_ctor_get(v_x_2272_, 0);
lean_dec(v_unused_2327_);
v___x_2294_ = v_x_2272_;
v_isShared_2295_ = v_isSharedCheck_2326_;
goto v_resetjp_2293_;
}
else
{
lean_dec(v_x_2272_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2326_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_node_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2325_; 
v_node_2296_ = lean_ctor_get(v_entry_2281_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_entry_2281_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2298_ = v_entry_2281_;
v_isShared_2299_ = v_isSharedCheck_2325_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_node_2296_);
lean_dec(v_entry_2281_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2325_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v_entries_2300_; size_t v___x_2301_; lean_object* v_newNode_2302_; lean_object* v___x_2303_; 
v_entries_2300_ = lean_array_set(v_es_2275_, v_j_2280_, v___x_2276_);
v___x_2301_ = lean_usize_shift_right(v_x_2273_, v___x_2277_);
v_newNode_2302_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2296_, v___x_2301_, v_x_2274_);
lean_inc_ref(v_newNode_2302_);
v___x_2303_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2302_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v___x_2305_; 
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v_newNode_2302_);
v___x_2305_ = v___x_2298_;
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
v___x_2306_ = lean_array_set(v_entries_2300_, v_j_2280_, v___x_2305_);
lean_dec(v_j_2280_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2306_);
v___x_2308_ = v___x_2294_;
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
lean_del_object(v___x_2298_);
v_val_2311_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_val_2311_);
lean_dec_ref(v___x_2303_);
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
v___x_2319_ = lean_array_set(v_entries_2300_, v_j_2280_, v___x_2318_);
lean_dec(v_j_2280_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2319_);
v___x_2321_ = v___x_2294_;
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
lean_dec(v_j_2280_);
return v_x_2272_;
}
}
}
else
{
lean_object* v_ks_2328_; lean_object* v_vs_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2343_; 
v_ks_2328_ = lean_ctor_get(v_x_2272_, 0);
v_vs_2329_ = lean_ctor_get(v_x_2272_, 1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_x_2272_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2331_ = v_x_2272_;
v_isShared_2332_ = v_isSharedCheck_2343_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_vs_2329_);
lean_inc(v_ks_2328_);
lean_dec(v_x_2272_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2343_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2328_, v_x_2274_);
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
lean_dec_ref(v___x_2333_);
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
size_t v_x_21947__boxed_2347_; lean_object* v_res_2348_; 
v_x_21947__boxed_2347_ = lean_unbox_usize(v_x_2345_);
lean_dec(v_x_2345_);
v_res_2348_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2344_, v_x_21947__boxed_2347_, v_x_2346_);
lean_dec_ref(v_x_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
uint64_t v___x_2351_; size_t v_h_2352_; lean_object* v___x_2353_; 
v___x_2351_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2350_);
v_h_2352_ = lean_uint64_to_usize(v___x_2351_);
v___x_2353_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2349_, v_h_2352_, v_x_2350_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2354_, lean_object* v_x_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2354_, v_x_2355_);
lean_dec_ref(v_x_2355_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
if (lean_obj_tag(v_as_2357_) == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_box(0);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
else
{
lean_object* v_head_2371_; lean_object* v_tail_2372_; lean_object* v___x_2373_; 
v_head_2371_ = lean_ctor_get(v_as_2357_, 0);
lean_inc(v_head_2371_);
v_tail_2372_ = lean_ctor_get(v_as_2357_, 1);
lean_inc(v_tail_2372_);
lean_dec_ref(v_as_2357_);
v___x_2373_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2371_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_dec_ref(v___x_2373_);
v_as_2357_ = v_tail_2372_;
goto _start;
}
else
{
lean_dec(v_tail_2372_);
return v___x_2373_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec(v___y_2376_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2388_, lean_object* v_vals_2389_, lean_object* v_i_2390_, lean_object* v_k_2391_){
_start:
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = lean_array_get_size(v_keys_2388_);
v___x_2393_ = lean_nat_dec_lt(v_i_2390_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; 
lean_dec(v_i_2390_);
v___x_2394_ = lean_box(0);
return v___x_2394_;
}
else
{
lean_object* v_k_x27_2395_; uint8_t v___x_2396_; 
v_k_x27_2395_ = lean_array_fget_borrowed(v_keys_2388_, v_i_2390_);
v___x_2396_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_2391_, v_k_x27_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_add(v_i_2390_, v___x_2397_);
lean_dec(v_i_2390_);
v_i_2390_ = v___x_2398_;
goto _start;
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_array_fget_borrowed(v_vals_2389_, v_i_2390_);
lean_dec(v_i_2390_);
lean_inc(v___x_2400_);
v___x_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
return v___x_2401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2402_, lean_object* v_vals_2403_, lean_object* v_i_2404_, lean_object* v_k_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2402_, v_vals_2403_, v_i_2404_, v_k_2405_);
lean_dec_ref(v_k_2405_);
lean_dec_ref(v_vals_2403_);
lean_dec_ref(v_keys_2402_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2407_, size_t v_x_2408_, lean_object* v_x_2409_){
_start:
{
if (lean_obj_tag(v_x_2407_) == 0)
{
lean_object* v_es_2410_; lean_object* v___x_2411_; size_t v___x_2412_; size_t v___x_2413_; size_t v___x_2414_; lean_object* v_j_2415_; lean_object* v___x_2416_; 
v_es_2410_ = lean_ctor_get(v_x_2407_, 0);
v___x_2411_ = lean_box(2);
v___x_2412_ = ((size_t)5ULL);
v___x_2413_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2414_ = lean_usize_land(v_x_2408_, v___x_2413_);
v_j_2415_ = lean_usize_to_nat(v___x_2414_);
v___x_2416_ = lean_array_get_borrowed(v___x_2411_, v_es_2410_, v_j_2415_);
lean_dec(v_j_2415_);
switch(lean_obj_tag(v___x_2416_))
{
case 0:
{
lean_object* v_key_2417_; lean_object* v_val_2418_; uint8_t v___x_2419_; 
v_key_2417_ = lean_ctor_get(v___x_2416_, 0);
v_val_2418_ = lean_ctor_get(v___x_2416_, 1);
v___x_2419_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2409_, v_key_2417_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_box(0);
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; 
lean_inc(v_val_2418_);
v___x_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_val_2418_);
return v___x_2421_;
}
}
case 1:
{
lean_object* v_node_2422_; size_t v___x_2423_; 
v_node_2422_ = lean_ctor_get(v___x_2416_, 0);
v___x_2423_ = lean_usize_shift_right(v_x_2408_, v___x_2412_);
v_x_2407_ = v_node_2422_;
v_x_2408_ = v___x_2423_;
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
v_ks_2426_ = lean_ctor_get(v_x_2407_, 0);
v_vs_2427_ = lean_ctor_get(v_x_2407_, 1);
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2426_, v_vs_2427_, v___x_2428_, v_x_2409_);
return v___x_2429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
size_t v_x_22166__boxed_2433_; lean_object* v_res_2434_; 
v_x_22166__boxed_2433_ = lean_unbox_usize(v_x_2431_);
lean_dec(v_x_2431_);
v_res_2434_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2430_, v_x_22166__boxed_2433_, v_x_2432_);
lean_dec_ref(v_x_2432_);
lean_dec_ref(v_x_2430_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
uint64_t v___x_2437_; size_t v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2436_);
v___x_2438_ = lean_uint64_to_usize(v___x_2437_);
v___x_2439_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2435_, v___x_2438_, v_x_2436_);
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
lean_object* v_head_2457_; lean_object* v_tail_2458_; lean_object* v___x_2459_; lean_object* v_toGoalState_2460_; lean_object* v_ematch_2461_; lean_object* v_delayedThmInsts_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_head_2457_ = lean_ctor_get(v_as_x27_2443_, 0);
v_tail_2458_ = lean_ctor_get(v_as_x27_2443_, 1);
v___x_2459_ = lean_st_ref_get(v___y_2445_);
v_toGoalState_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc_ref(v_toGoalState_2460_);
lean_dec(v___x_2459_);
v_ematch_2461_ = lean_ctor_get(v_toGoalState_2460_, 12);
lean_inc_ref(v_ematch_2461_);
lean_dec_ref(v_toGoalState_2460_);
v_delayedThmInsts_2462_ = lean_ctor_get(v_ematch_2461_, 10);
lean_inc_ref(v_delayedThmInsts_2462_);
lean_dec_ref(v_ematch_2461_);
v___x_2463_ = lean_box(0);
v___x_2464_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2462_, v_head_2457_);
lean_dec_ref(v_delayedThmInsts_2462_);
if (lean_obj_tag(v___x_2464_) == 1)
{
lean_object* v_val_2465_; lean_object* v___x_2466_; lean_object* v_toGoalState_2467_; lean_object* v_ematch_2468_; lean_object* v_mvarId_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2523_; 
v_val_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_val_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = lean_st_ref_take(v___y_2445_);
v_toGoalState_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc_ref(v_toGoalState_2467_);
v_ematch_2468_ = lean_ctor_get(v_toGoalState_2467_, 12);
lean_inc_ref(v_ematch_2468_);
v_mvarId_2469_ = lean_ctor_get(v___x_2466_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v___x_2466_, 0);
lean_dec(v_unused_2524_);
v___x_2471_ = v___x_2466_;
v_isShared_2472_ = v_isSharedCheck_2523_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_mvarId_2469_);
lean_dec(v___x_2466_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2523_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v_nextDeclIdx_2473_; lean_object* v_enodeMap_2474_; lean_object* v_exprs_2475_; lean_object* v_parents_2476_; lean_object* v_congrTable_2477_; lean_object* v_appMap_2478_; lean_object* v_indicesFound_2479_; lean_object* v_newFacts_2480_; uint8_t v_inconsistent_2481_; lean_object* v_nextIdx_2482_; lean_object* v_newRawFacts_2483_; lean_object* v_facts_2484_; lean_object* v_extThms_2485_; lean_object* v_inj_2486_; lean_object* v_split_2487_; lean_object* v_clean_2488_; lean_object* v_sstates_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2521_; 
v_nextDeclIdx_2473_ = lean_ctor_get(v_toGoalState_2467_, 0);
v_enodeMap_2474_ = lean_ctor_get(v_toGoalState_2467_, 1);
v_exprs_2475_ = lean_ctor_get(v_toGoalState_2467_, 2);
v_parents_2476_ = lean_ctor_get(v_toGoalState_2467_, 3);
v_congrTable_2477_ = lean_ctor_get(v_toGoalState_2467_, 4);
v_appMap_2478_ = lean_ctor_get(v_toGoalState_2467_, 5);
v_indicesFound_2479_ = lean_ctor_get(v_toGoalState_2467_, 6);
v_newFacts_2480_ = lean_ctor_get(v_toGoalState_2467_, 7);
v_inconsistent_2481_ = lean_ctor_get_uint8(v_toGoalState_2467_, sizeof(void*)*17);
v_nextIdx_2482_ = lean_ctor_get(v_toGoalState_2467_, 8);
v_newRawFacts_2483_ = lean_ctor_get(v_toGoalState_2467_, 9);
v_facts_2484_ = lean_ctor_get(v_toGoalState_2467_, 10);
v_extThms_2485_ = lean_ctor_get(v_toGoalState_2467_, 11);
v_inj_2486_ = lean_ctor_get(v_toGoalState_2467_, 13);
v_split_2487_ = lean_ctor_get(v_toGoalState_2467_, 14);
v_clean_2488_ = lean_ctor_get(v_toGoalState_2467_, 15);
v_sstates_2489_ = lean_ctor_get(v_toGoalState_2467_, 16);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_toGoalState_2467_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; 
v_unused_2522_ = lean_ctor_get(v_toGoalState_2467_, 12);
lean_dec(v_unused_2522_);
v___x_2491_ = v_toGoalState_2467_;
v_isShared_2492_ = v_isSharedCheck_2521_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_sstates_2489_);
lean_inc(v_clean_2488_);
lean_inc(v_split_2487_);
lean_inc(v_inj_2486_);
lean_inc(v_extThms_2485_);
lean_inc(v_facts_2484_);
lean_inc(v_newRawFacts_2483_);
lean_inc(v_nextIdx_2482_);
lean_inc(v_newFacts_2480_);
lean_inc(v_indicesFound_2479_);
lean_inc(v_appMap_2478_);
lean_inc(v_congrTable_2477_);
lean_inc(v_parents_2476_);
lean_inc(v_exprs_2475_);
lean_inc(v_enodeMap_2474_);
lean_inc(v_nextDeclIdx_2473_);
lean_dec(v_toGoalState_2467_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2521_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_thmMap_2493_; lean_object* v_gmt_2494_; lean_object* v_thms_2495_; lean_object* v_newThms_2496_; lean_object* v_numInstances_2497_; lean_object* v_numDelayedInstances_2498_; lean_object* v_num_2499_; lean_object* v_preInstances_2500_; lean_object* v_nextThmIdx_2501_; lean_object* v_matchEqNames_2502_; lean_object* v_delayedThmInsts_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2520_; 
v_thmMap_2493_ = lean_ctor_get(v_ematch_2468_, 0);
v_gmt_2494_ = lean_ctor_get(v_ematch_2468_, 1);
v_thms_2495_ = lean_ctor_get(v_ematch_2468_, 2);
v_newThms_2496_ = lean_ctor_get(v_ematch_2468_, 3);
v_numInstances_2497_ = lean_ctor_get(v_ematch_2468_, 4);
v_numDelayedInstances_2498_ = lean_ctor_get(v_ematch_2468_, 5);
v_num_2499_ = lean_ctor_get(v_ematch_2468_, 6);
v_preInstances_2500_ = lean_ctor_get(v_ematch_2468_, 7);
v_nextThmIdx_2501_ = lean_ctor_get(v_ematch_2468_, 8);
v_matchEqNames_2502_ = lean_ctor_get(v_ematch_2468_, 9);
v_delayedThmInsts_2503_ = lean_ctor_get(v_ematch_2468_, 10);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_ematch_2468_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2505_ = v_ematch_2468_;
v_isShared_2506_ = v_isSharedCheck_2520_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_delayedThmInsts_2503_);
lean_inc(v_matchEqNames_2502_);
lean_inc(v_nextThmIdx_2501_);
lean_inc(v_preInstances_2500_);
lean_inc(v_num_2499_);
lean_inc(v_numDelayedInstances_2498_);
lean_inc(v_numInstances_2497_);
lean_inc(v_newThms_2496_);
lean_inc(v_thms_2495_);
lean_inc(v_gmt_2494_);
lean_inc(v_thmMap_2493_);
lean_dec(v_ematch_2468_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2520_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2503_, v_head_2457_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 10, v___x_2507_);
v___x_2509_ = v___x_2505_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_thmMap_2493_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_gmt_2494_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_thms_2495_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_newThms_2496_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_numInstances_2497_);
lean_ctor_set(v_reuseFailAlloc_2519_, 5, v_numDelayedInstances_2498_);
lean_ctor_set(v_reuseFailAlloc_2519_, 6, v_num_2499_);
lean_ctor_set(v_reuseFailAlloc_2519_, 7, v_preInstances_2500_);
lean_ctor_set(v_reuseFailAlloc_2519_, 8, v_nextThmIdx_2501_);
lean_ctor_set(v_reuseFailAlloc_2519_, 9, v_matchEqNames_2502_);
lean_ctor_set(v_reuseFailAlloc_2519_, 10, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2511_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 12, v___x_2509_);
v___x_2511_ = v___x_2491_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_nextDeclIdx_2473_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_enodeMap_2474_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_exprs_2475_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_parents_2476_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_congrTable_2477_);
lean_ctor_set(v_reuseFailAlloc_2518_, 5, v_appMap_2478_);
lean_ctor_set(v_reuseFailAlloc_2518_, 6, v_indicesFound_2479_);
lean_ctor_set(v_reuseFailAlloc_2518_, 7, v_newFacts_2480_);
lean_ctor_set(v_reuseFailAlloc_2518_, 8, v_nextIdx_2482_);
lean_ctor_set(v_reuseFailAlloc_2518_, 9, v_newRawFacts_2483_);
lean_ctor_set(v_reuseFailAlloc_2518_, 10, v_facts_2484_);
lean_ctor_set(v_reuseFailAlloc_2518_, 11, v_extThms_2485_);
lean_ctor_set(v_reuseFailAlloc_2518_, 12, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2518_, 13, v_inj_2486_);
lean_ctor_set(v_reuseFailAlloc_2518_, 14, v_split_2487_);
lean_ctor_set(v_reuseFailAlloc_2518_, 15, v_clean_2488_);
lean_ctor_set(v_reuseFailAlloc_2518_, 16, v_sstates_2489_);
lean_ctor_set_uint8(v_reuseFailAlloc_2518_, sizeof(void*)*17, v_inconsistent_2481_);
v___x_2511_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2513_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2511_);
v___x_2513_ = v___x_2471_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_mvarId_2469_);
v___x_2513_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_st_ref_set(v___y_2445_, v___x_2513_);
v___x_2515_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2465_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_dec_ref(v___x_2515_);
v_as_x27_2443_ = v_tail_2458_;
v_b_2444_ = v___x_2463_;
goto _start;
}
else
{
return v___x_2515_;
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
v_b_2444_ = v___x_2463_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2526_, lean_object* v_b_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2526_, v_b_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec(v_as_x27_2526_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2541_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2581_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2581_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2581_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
uint8_t v___x_2557_; 
v___x_2557_ = lean_unbox(v_a_2553_);
lean_dec(v_a_2553_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; lean_object* v_toGoalState_2559_; lean_object* v_ematch_2560_; lean_object* v_delayedThmInsts_2561_; uint8_t v___x_2562_; 
v___x_2558_ = lean_st_ref_get(v_a_2541_);
v_toGoalState_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc_ref(v_toGoalState_2559_);
lean_dec(v___x_2558_);
v_ematch_2560_ = lean_ctor_get(v_toGoalState_2559_, 12);
lean_inc_ref(v_ematch_2560_);
lean_dec_ref(v_toGoalState_2559_);
v_delayedThmInsts_2561_ = lean_ctor_get(v_ematch_2560_, 10);
lean_inc_ref(v_delayedThmInsts_2561_);
lean_dec_ref(v_ematch_2560_);
v___x_2562_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2561_);
lean_dec_ref(v_delayedThmInsts_2561_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_del_object(v___x_2555_);
v___x_2563_ = lean_box(0);
v___x_2564_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2540_, v___x_2563_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2571_ == 0)
{
lean_object* v_unused_2572_; 
v_unused_2572_ = lean_ctor_get(v___x_2564_, 0);
lean_dec(v_unused_2572_);
v___x_2566_ = v___x_2564_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_dec(v___x_2564_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2563_);
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2563_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
else
{
return v___x_2564_;
}
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_box(0);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2573_);
v___x_2575_ = v___x_2555_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_box(0);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2577_);
v___x_2579_ = v___x_2555_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_a_2582_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2552_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2552_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec(v_toPropagateDown_2590_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2603_, lean_object* v_x_2604_, lean_object* v_x_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2604_, v_x_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2607_, lean_object* v_x_2608_, lean_object* v_x_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2607_, v_x_2608_, v_x_2609_);
lean_dec_ref(v_x_2609_);
lean_dec_ref(v_x_2608_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2611_, lean_object* v_x_2612_, lean_object* v_x_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2612_, v_x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2615_, lean_object* v_x_2616_, lean_object* v_x_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2615_, v_x_2616_, v_x_2617_);
lean_dec_ref(v_x_2617_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2619_, lean_object* v_as_x27_2620_, lean_object* v_b_2621_, lean_object* v_a_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2620_, v_b_2621_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2635_, lean_object* v_as_x27_2636_, lean_object* v_b_2637_, lean_object* v_a_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2635_, v_as_x27_2636_, v_b_2637_, v_a_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec(v_as_x27_2636_);
lean_dec(v_as_2635_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2651_, lean_object* v_x_2652_, size_t v_x_2653_, lean_object* v_x_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2652_, v_x_2653_, v_x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2656_, lean_object* v_x_2657_, lean_object* v_x_2658_, lean_object* v_x_2659_){
_start:
{
size_t v_x_22463__boxed_2660_; lean_object* v_res_2661_; 
v_x_22463__boxed_2660_ = lean_unbox_usize(v_x_2658_);
lean_dec(v_x_2658_);
v_res_2661_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2656_, v_x_2657_, v_x_22463__boxed_2660_, v_x_2659_);
lean_dec_ref(v_x_2659_);
lean_dec_ref(v_x_2657_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2662_, lean_object* v_x_2663_, size_t v_x_2664_, lean_object* v_x_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2663_, v_x_2664_, v_x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2667_, lean_object* v_x_2668_, lean_object* v_x_2669_, lean_object* v_x_2670_){
_start:
{
size_t v_x_22474__boxed_2671_; lean_object* v_res_2672_; 
v_x_22474__boxed_2671_ = lean_unbox_usize(v_x_2669_);
lean_dec(v_x_2669_);
v_res_2672_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2667_, v_x_2668_, v_x_22474__boxed_2671_, v_x_2670_);
lean_dec_ref(v_x_2670_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2673_, lean_object* v_keys_2674_, lean_object* v_vals_2675_, lean_object* v_heq_2676_, lean_object* v_i_2677_, lean_object* v_k_2678_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2674_, v_vals_2675_, v_i_2677_, v_k_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2680_, lean_object* v_keys_2681_, lean_object* v_vals_2682_, lean_object* v_heq_2683_, lean_object* v_i_2684_, lean_object* v_k_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2680_, v_keys_2681_, v_vals_2682_, v_heq_2683_, v_i_2684_, v_k_2685_);
lean_dec_ref(v_k_2685_);
lean_dec_ref(v_vals_2682_);
lean_dec_ref(v_keys_2681_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2687_, lean_object* v_keys_2688_, lean_object* v_vals_2689_, lean_object* v_i_2690_, lean_object* v_k_2691_){
_start:
{
lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2692_ = lean_array_get_size(v_keys_2688_);
v___x_2693_ = lean_nat_dec_lt(v_i_2690_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; 
lean_dec_ref(v_k_2691_);
lean_dec(v_i_2690_);
v___x_2694_ = lean_box(0);
return v___x_2694_;
}
else
{
lean_object* v_k_x27_2695_; uint8_t v___x_2696_; 
v_k_x27_2695_ = lean_array_fget_borrowed(v_keys_2688_, v_i_2690_);
lean_inc(v_k_x27_2695_);
lean_inc_ref(v_k_2691_);
v___x_2696_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2687_, v_k_2691_, v_k_x27_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = lean_nat_add(v_i_2690_, v___x_2697_);
lean_dec(v_i_2690_);
v_i_2690_ = v___x_2698_;
goto _start;
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
lean_dec_ref(v_k_2691_);
v___x_2700_ = lean_array_fget_borrowed(v_vals_2689_, v_i_2690_);
lean_dec(v_i_2690_);
lean_inc(v___x_2700_);
lean_inc(v_k_x27_2695_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_k_x27_2695_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2703_, lean_object* v_keys_2704_, lean_object* v_vals_2705_, lean_object* v_i_2706_, lean_object* v_k_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2703_, v_keys_2704_, v_vals_2705_, v_i_2706_, v_k_2707_);
lean_dec_ref(v_vals_2705_);
lean_dec_ref(v_keys_2704_);
lean_dec_ref(v___x_2703_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2709_, lean_object* v_x_2710_, size_t v_x_2711_, lean_object* v_x_2712_){
_start:
{
if (lean_obj_tag(v_x_2710_) == 0)
{
lean_object* v_es_2713_; lean_object* v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; lean_object* v_j_2718_; lean_object* v___x_2719_; 
v_es_2713_ = lean_ctor_get(v_x_2710_, 0);
lean_inc_ref(v_es_2713_);
lean_dec_ref(v_x_2710_);
v___x_2714_ = lean_box(2);
v___x_2715_ = ((size_t)5ULL);
v___x_2716_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2717_ = lean_usize_land(v_x_2711_, v___x_2716_);
v_j_2718_ = lean_usize_to_nat(v___x_2717_);
v___x_2719_ = lean_array_get(v___x_2714_, v_es_2713_, v_j_2718_);
lean_dec(v_j_2718_);
lean_dec_ref(v_es_2713_);
switch(lean_obj_tag(v___x_2719_))
{
case 0:
{
lean_object* v_key_2720_; lean_object* v_val_2721_; uint8_t v___x_2722_; 
v_key_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc_n(v_key_2720_, 2);
v_val_2721_ = lean_ctor_get(v___x_2719_, 1);
lean_inc(v_val_2721_);
lean_dec_ref(v___x_2719_);
v___x_2722_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2709_, v_x_2712_, v_key_2720_);
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
lean_object* v_node_2726_; size_t v___x_2727_; 
v_node_2726_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_node_2726_);
lean_dec_ref(v___x_2719_);
v___x_2727_ = lean_usize_shift_right(v_x_2711_, v___x_2715_);
v_x_2710_ = v_node_2726_;
v_x_2711_ = v___x_2727_;
goto _start;
}
default: 
{
lean_object* v___x_2729_; 
lean_dec_ref(v_x_2712_);
v___x_2729_ = lean_box(0);
return v___x_2729_;
}
}
}
else
{
lean_object* v_ks_2730_; lean_object* v_vs_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v_ks_2730_ = lean_ctor_get(v_x_2710_, 0);
lean_inc_ref(v_ks_2730_);
v_vs_2731_ = lean_ctor_get(v_x_2710_, 1);
lean_inc_ref(v_vs_2731_);
lean_dec_ref(v_x_2710_);
v___x_2732_ = lean_unsigned_to_nat(0u);
v___x_2733_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2709_, v_ks_2730_, v_vs_2731_, v___x_2732_, v_x_2712_);
lean_dec_ref(v_vs_2731_);
lean_dec_ref(v_ks_2730_);
return v___x_2733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2734_, lean_object* v_x_2735_, lean_object* v_x_2736_, lean_object* v_x_2737_){
_start:
{
size_t v_x_27624__boxed_2738_; lean_object* v_res_2739_; 
v_x_27624__boxed_2738_ = lean_unbox_usize(v_x_2736_);
lean_dec(v_x_2736_);
v_res_2739_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2734_, v_x_2735_, v_x_27624__boxed_2738_, v_x_2737_);
lean_dec_ref(v___x_2734_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2740_, lean_object* v_x_2741_, lean_object* v_x_2742_){
_start:
{
uint64_t v___x_2743_; size_t v___x_2744_; lean_object* v___x_2745_; 
lean_inc_ref(v_x_2742_);
v___x_2743_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2740_, v_x_2742_);
v___x_2744_ = lean_uint64_to_usize(v___x_2743_);
lean_inc_ref(v_x_2741_);
v___x_2745_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2740_, v_x_2741_, v___x_2744_, v_x_2742_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2746_, v_x_2747_, v_x_2748_);
lean_dec_ref(v_x_2747_);
lean_dec_ref(v___x_2746_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_){
_start:
{
lean_object* v_ks_2755_; lean_object* v_vs_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2780_; 
v_ks_2755_ = lean_ctor_get(v_x_2751_, 0);
v_vs_2756_ = lean_ctor_get(v_x_2751_, 1);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_x_2751_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2758_ = v_x_2751_;
v_isShared_2759_ = v_isSharedCheck_2780_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_vs_2756_);
lean_inc(v_ks_2755_);
lean_dec(v_x_2751_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2780_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; uint8_t v___x_2761_; 
v___x_2760_ = lean_array_get_size(v_ks_2755_);
v___x_2761_ = lean_nat_dec_lt(v_x_2752_, v___x_2760_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
lean_dec(v_x_2752_);
v___x_2762_ = lean_array_push(v_ks_2755_, v_x_2753_);
v___x_2763_ = lean_array_push(v_vs_2756_, v_x_2754_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___x_2763_);
lean_ctor_set(v___x_2758_, 0, v___x_2762_);
v___x_2765_ = v___x_2758_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2762_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
else
{
lean_object* v_k_x27_2767_; uint8_t v___x_2768_; 
v_k_x27_2767_ = lean_array_fget_borrowed(v_ks_2755_, v_x_2752_);
lean_inc(v_k_x27_2767_);
lean_inc_ref(v_x_2753_);
v___x_2768_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2750_, v_x_2753_, v_k_x27_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2770_; 
if (v_isShared_2759_ == 0)
{
v___x_2770_ = v___x_2758_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_ks_2755_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_vs_2756_);
v___x_2770_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_unsigned_to_nat(1u);
v___x_2772_ = lean_nat_add(v_x_2752_, v___x_2771_);
lean_dec(v_x_2752_);
v_x_2751_ = v___x_2770_;
v_x_2752_ = v___x_2772_;
goto _start;
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2775_ = lean_array_fset(v_ks_2755_, v_x_2752_, v_x_2753_);
v___x_2776_ = lean_array_fset(v_vs_2756_, v_x_2752_, v_x_2754_);
lean_dec(v_x_2752_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___x_2776_);
lean_ctor_set(v___x_2758_, 0, v___x_2775_);
v___x_2778_ = v___x_2758_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2781_, lean_object* v_x_2782_, lean_object* v_x_2783_, lean_object* v_x_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2781_, v_x_2782_, v_x_2783_, v_x_2784_, v_x_2785_);
lean_dec_ref(v___x_2781_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2787_, lean_object* v_n_2788_, lean_object* v_k_2789_, lean_object* v_v_2790_){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2787_, v_n_2788_, v___x_2791_, v_k_2789_, v_v_2790_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2793_, lean_object* v_n_2794_, lean_object* v_k_2795_, lean_object* v_v_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2793_, v_n_2794_, v_k_2795_, v_v_2796_);
lean_dec_ref(v___x_2793_);
return v_res_2797_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2799_, lean_object* v_x_2800_, size_t v_x_2801_, size_t v_x_2802_, lean_object* v_x_2803_, lean_object* v_x_2804_){
_start:
{
if (lean_obj_tag(v_x_2800_) == 0)
{
lean_object* v_es_2805_; size_t v___x_2806_; size_t v___x_2807_; size_t v___x_2808_; size_t v___x_2809_; lean_object* v_j_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v_es_2805_ = lean_ctor_get(v_x_2800_, 0);
v___x_2806_ = ((size_t)5ULL);
v___x_2807_ = ((size_t)1ULL);
v___x_2808_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2809_ = lean_usize_land(v_x_2801_, v___x_2808_);
v_j_2810_ = lean_usize_to_nat(v___x_2809_);
v___x_2811_ = lean_array_get_size(v_es_2805_);
v___x_2812_ = lean_nat_dec_lt(v_j_2810_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_dec(v_j_2810_);
lean_dec(v_x_2804_);
lean_dec_ref(v_x_2803_);
return v_x_2800_;
}
else
{
lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2849_; 
lean_inc_ref(v_es_2805_);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_x_2800_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v_x_2800_, 0);
lean_dec(v_unused_2850_);
v___x_2814_ = v_x_2800_;
v_isShared_2815_ = v_isSharedCheck_2849_;
goto v_resetjp_2813_;
}
else
{
lean_dec(v_x_2800_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2849_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_v_2816_; lean_object* v___x_2817_; lean_object* v_xs_x27_2818_; lean_object* v___y_2820_; 
v_v_2816_ = lean_array_fget(v_es_2805_, v_j_2810_);
v___x_2817_ = lean_box(0);
v_xs_x27_2818_ = lean_array_fset(v_es_2805_, v_j_2810_, v___x_2817_);
switch(lean_obj_tag(v_v_2816_))
{
case 0:
{
lean_object* v_key_2825_; lean_object* v_val_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2836_; 
v_key_2825_ = lean_ctor_get(v_v_2816_, 0);
v_val_2826_ = lean_ctor_get(v_v_2816_, 1);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_v_2816_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2828_ = v_v_2816_;
v_isShared_2829_ = v_isSharedCheck_2836_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_val_2826_);
lean_inc(v_key_2825_);
lean_dec(v_v_2816_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2836_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
uint8_t v___x_2830_; 
lean_inc(v_key_2825_);
lean_inc_ref(v_x_2803_);
v___x_2830_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2799_, v_x_2803_, v_key_2825_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_del_object(v___x_2828_);
v___x_2831_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2825_, v_val_2826_, v_x_2803_, v_x_2804_);
v___x_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
v___y_2820_ = v___x_2832_;
goto v___jp_2819_;
}
else
{
lean_object* v___x_2834_; 
lean_dec(v_val_2826_);
lean_dec(v_key_2825_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 1, v_x_2804_);
lean_ctor_set(v___x_2828_, 0, v_x_2803_);
v___x_2834_ = v___x_2828_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_x_2803_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_x_2804_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
v___y_2820_ = v___x_2834_;
goto v___jp_2819_;
}
}
}
}
case 1:
{
lean_object* v_node_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2847_; 
v_node_2837_ = lean_ctor_get(v_v_2816_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_v_2816_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2839_ = v_v_2816_;
v_isShared_2840_ = v_isSharedCheck_2847_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_node_2837_);
lean_dec(v_v_2816_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2847_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
size_t v___x_2841_; size_t v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2841_ = lean_usize_shift_right(v_x_2801_, v___x_2806_);
v___x_2842_ = lean_usize_add(v_x_2802_, v___x_2807_);
v___x_2843_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2799_, v_node_2837_, v___x_2841_, v___x_2842_, v_x_2803_, v_x_2804_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2843_);
v___x_2845_ = v___x_2839_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
v___y_2820_ = v___x_2845_;
goto v___jp_2819_;
}
}
}
default: 
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2848_, 0, v_x_2803_);
lean_ctor_set(v___x_2848_, 1, v_x_2804_);
v___y_2820_ = v___x_2848_;
goto v___jp_2819_;
}
}
v___jp_2819_:
{
lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2821_ = lean_array_fset(v_xs_x27_2818_, v_j_2810_, v___y_2820_);
lean_dec(v_j_2810_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2821_);
v___x_2823_ = v___x_2814_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
else
{
lean_object* v_ks_2851_; lean_object* v_vs_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2872_; 
v_ks_2851_ = lean_ctor_get(v_x_2800_, 0);
v_vs_2852_ = lean_ctor_get(v_x_2800_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_x_2800_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2854_ = v_x_2800_;
v_isShared_2855_ = v_isSharedCheck_2872_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_vs_2852_);
lean_inc(v_ks_2851_);
lean_dec(v_x_2800_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2872_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_ks_2851_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_vs_2852_);
v___x_2857_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v_newNode_2858_; uint8_t v___y_2860_; size_t v___x_2866_; uint8_t v___x_2867_; 
v_newNode_2858_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2799_, v___x_2857_, v_x_2803_, v_x_2804_);
v___x_2866_ = ((size_t)7ULL);
v___x_2867_ = lean_usize_dec_le(v___x_2866_, v_x_2802_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2868_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2858_);
v___x_2869_ = lean_unsigned_to_nat(4u);
v___x_2870_ = lean_nat_dec_lt(v___x_2868_, v___x_2869_);
lean_dec(v___x_2868_);
v___y_2860_ = v___x_2870_;
goto v___jp_2859_;
}
else
{
v___y_2860_ = v___x_2867_;
goto v___jp_2859_;
}
v___jp_2859_:
{
if (v___y_2860_ == 0)
{
lean_object* v_ks_2861_; lean_object* v_vs_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_ks_2861_ = lean_ctor_get(v_newNode_2858_, 0);
lean_inc_ref(v_ks_2861_);
v_vs_2862_ = lean_ctor_get(v_newNode_2858_, 1);
lean_inc_ref(v_vs_2862_);
lean_dec_ref(v_newNode_2858_);
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2865_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2799_, v_x_2802_, v_ks_2861_, v_vs_2862_, v___x_2863_, v___x_2864_);
lean_dec_ref(v_vs_2862_);
lean_dec_ref(v_ks_2861_);
return v___x_2865_;
}
else
{
return v_newNode_2858_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2873_, size_t v_depth_2874_, lean_object* v_keys_2875_, lean_object* v_vals_2876_, lean_object* v_i_2877_, lean_object* v_entries_2878_){
_start:
{
lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = lean_array_get_size(v_keys_2875_);
v___x_2880_ = lean_nat_dec_lt(v_i_2877_, v___x_2879_);
if (v___x_2880_ == 0)
{
lean_dec(v_i_2877_);
return v_entries_2878_;
}
else
{
lean_object* v_k_2881_; lean_object* v_v_2882_; uint64_t v___x_2883_; size_t v_h_2884_; size_t v___x_2885_; lean_object* v___x_2886_; size_t v___x_2887_; size_t v___x_2888_; size_t v___x_2889_; size_t v_h_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_k_2881_ = lean_array_fget_borrowed(v_keys_2875_, v_i_2877_);
v_v_2882_ = lean_array_fget_borrowed(v_vals_2876_, v_i_2877_);
lean_inc_n(v_k_2881_, 2);
v___x_2883_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2873_, v_k_2881_);
v_h_2884_ = lean_uint64_to_usize(v___x_2883_);
v___x_2885_ = ((size_t)5ULL);
v___x_2886_ = lean_unsigned_to_nat(1u);
v___x_2887_ = ((size_t)1ULL);
v___x_2888_ = lean_usize_sub(v_depth_2874_, v___x_2887_);
v___x_2889_ = lean_usize_mul(v___x_2885_, v___x_2888_);
v_h_2890_ = lean_usize_shift_right(v_h_2884_, v___x_2889_);
v___x_2891_ = lean_nat_add(v_i_2877_, v___x_2886_);
lean_dec(v_i_2877_);
lean_inc(v_v_2882_);
v___x_2892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2873_, v_entries_2878_, v_h_2890_, v_depth_2874_, v_k_2881_, v_v_2882_);
v_i_2877_ = v___x_2891_;
v_entries_2878_ = v___x_2892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2894_, lean_object* v_depth_2895_, lean_object* v_keys_2896_, lean_object* v_vals_2897_, lean_object* v_i_2898_, lean_object* v_entries_2899_){
_start:
{
size_t v_depth_boxed_2900_; lean_object* v_res_2901_; 
v_depth_boxed_2900_ = lean_unbox_usize(v_depth_2895_);
lean_dec(v_depth_2895_);
v_res_2901_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2894_, v_depth_boxed_2900_, v_keys_2896_, v_vals_2897_, v_i_2898_, v_entries_2899_);
lean_dec_ref(v_vals_2897_);
lean_dec_ref(v_keys_2896_);
lean_dec_ref(v___x_2894_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2902_, lean_object* v_x_2903_, lean_object* v_x_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_){
_start:
{
size_t v_x_27786__boxed_2908_; size_t v_x_27787__boxed_2909_; lean_object* v_res_2910_; 
v_x_27786__boxed_2908_ = lean_unbox_usize(v_x_2904_);
lean_dec(v_x_2904_);
v_x_27787__boxed_2909_ = lean_unbox_usize(v_x_2905_);
lean_dec(v_x_2905_);
v_res_2910_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2902_, v_x_2903_, v_x_27786__boxed_2908_, v_x_27787__boxed_2909_, v_x_2906_, v_x_2907_);
lean_dec_ref(v___x_2902_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
uint64_t v___x_2915_; size_t v___x_2916_; size_t v___x_2917_; lean_object* v___x_2918_; 
lean_inc_ref(v_x_2913_);
v___x_2915_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2911_, v_x_2913_);
v___x_2916_ = lean_uint64_to_usize(v___x_2915_);
v___x_2917_ = ((size_t)1ULL);
v___x_2918_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2911_, v_x_2912_, v___x_2916_, v___x_2917_, v_x_2913_, v_x_2914_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2919_, lean_object* v_x_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2919_, v_x_2920_, v_x_2921_, v_x_2922_);
lean_dec_ref(v___x_2919_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2928_, lean_object* v_rootNew_2929_, uint8_t v_a_2930_, lean_object* v_a_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; lean_object* v_snd_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_3107_; 
v___x_2939_ = lean_st_ref_get(v___y_2932_);
v_snd_2940_ = lean_ctor_get(v_a_2931_, 1);
v_isSharedCheck_3107_ = !lean_is_exclusive(v_a_2931_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v_a_2931_, 0);
lean_dec(v_unused_3108_);
v___x_2942_ = v_a_2931_;
v_isShared_2943_ = v_isSharedCheck_3107_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snd_2940_);
lean_dec(v_a_2931_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_3107_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; 
lean_inc(v_snd_2940_);
v___x_2944_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2939_, v_snd_2940_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___x_2939_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3098_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_3098_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3098_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_self_2949_; lean_object* v_next_2950_; lean_object* v_congr_2951_; lean_object* v_target_x3f_2952_; lean_object* v_proof_x3f_2953_; uint8_t v_flipped_2954_; lean_object* v_size_2955_; uint8_t v_interpreted_2956_; uint8_t v_ctor_2957_; uint8_t v_hasLambdas_2958_; uint8_t v_heqProofs_2959_; lean_object* v_idx_2960_; lean_object* v_generation_2961_; lean_object* v_mt_2962_; lean_object* v_sTerms_2963_; uint8_t v_funCC_2964_; lean_object* v_ematchDiagSource_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3096_; 
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
v_isSharedCheck_3096_ = !lean_is_exclusive(v_a_2945_);
if (v_isSharedCheck_3096_ == 0)
{
lean_object* v_unused_3097_; 
v_unused_3097_ = lean_ctor_get(v_a_2945_, 2);
lean_dec(v_unused_3097_);
v___x_2967_ = v_a_2945_;
v_isShared_2968_ = v_isSharedCheck_3096_;
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
v_isShared_2968_ = v_isSharedCheck_3096_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___y_2984_; lean_object* v___x_2994_; 
v___x_2969_ = lean_box(0);
lean_inc(v_ematchDiagSource_2965_);
lean_inc(v_sTerms_2963_);
lean_inc(v_mt_2962_);
lean_inc(v_generation_2961_);
lean_inc(v_idx_2960_);
lean_inc(v_size_2955_);
lean_inc(v_proof_x3f_2953_);
lean_inc(v_target_x3f_2952_);
lean_inc_ref(v_rootNew_2929_);
lean_inc_ref(v_next_2950_);
lean_inc_ref(v_self_2949_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 2, v_rootNew_2929_);
v___x_2994_ = v___x_2967_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_self_2949_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_next_2950_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_rootNew_2929_);
lean_ctor_set(v_reuseFailAlloc_3095_, 3, v_congr_2951_);
lean_ctor_set(v_reuseFailAlloc_3095_, 4, v_target_x3f_2952_);
lean_ctor_set(v_reuseFailAlloc_3095_, 5, v_proof_x3f_2953_);
lean_ctor_set(v_reuseFailAlloc_3095_, 6, v_size_2955_);
lean_ctor_set(v_reuseFailAlloc_3095_, 7, v_idx_2960_);
lean_ctor_set(v_reuseFailAlloc_3095_, 8, v_generation_2961_);
lean_ctor_set(v_reuseFailAlloc_3095_, 9, v_mt_2962_);
lean_ctor_set(v_reuseFailAlloc_3095_, 10, v_sTerms_2963_);
lean_ctor_set(v_reuseFailAlloc_3095_, 11, v_ematchDiagSource_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_3095_, sizeof(void*)*12, v_flipped_2954_);
lean_ctor_set_uint8(v_reuseFailAlloc_3095_, sizeof(void*)*12 + 1, v_interpreted_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_3095_, sizeof(void*)*12 + 2, v_ctor_2957_);
lean_ctor_set_uint8(v_reuseFailAlloc_3095_, sizeof(void*)*12 + 3, v_hasLambdas_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3095_, sizeof(void*)*12 + 4, v_heqProofs_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_3095_, sizeof(void*)*12 + 5, v_funCC_2964_);
v___x_2994_ = v_reuseFailAlloc_3095_;
goto v_reusejp_2993_;
}
v___jp_2970_:
{
uint8_t v___x_2971_; 
v___x_2971_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_2950_, v_lhs_2928_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2973_; 
lean_del_object(v___x_2947_);
lean_dec(v_snd_2940_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v_next_2950_);
lean_ctor_set(v___x_2942_, 0, v___x_2969_);
v___x_2973_ = v___x_2942_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_next_2950_);
v___x_2973_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
v_a_2931_ = v___x_2973_;
goto _start;
}
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
lean_dec_ref(v_next_2950_);
lean_dec_ref(v_rootNew_2929_);
v___x_2976_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2976_);
v___x_2978_ = v___x_2942_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2976_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_snd_2940_);
v___x_2978_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2980_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_2978_);
v___x_2980_ = v___x_2947_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
v___jp_2983_:
{
if (lean_obj_tag(v___y_2984_) == 0)
{
lean_dec_ref(v___y_2984_);
goto v___jp_2970_;
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec_ref(v_next_2950_);
lean_del_object(v___x_2947_);
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2929_);
v_a_2985_ = lean_ctor_get(v___y_2984_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___y_2984_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___y_2984_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___y_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; 
lean_inc_ref(v___x_2994_);
lean_inc_ref(v_self_2949_);
v___x_2995_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2949_, v___x_2994_, v___y_2932_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_dec_ref(v___x_2995_);
if (v_a_2930_ == 0)
{
lean_dec_ref(v___x_2994_);
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_self_2949_);
goto v___jp_2970_;
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2996_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2997_ = lean_unsigned_to_nat(3u);
v___x_2998_ = l_Lean_Expr_isAppOfArity(v_self_2949_, v___x_2996_, v___x_2997_);
if (v___x_2998_ == 0)
{
lean_dec_ref(v___x_2994_);
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_self_2949_);
goto v___jp_2970_;
}
else
{
uint8_t v___x_2999_; 
v___x_2999_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2994_);
lean_dec_ref(v___x_2994_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; lean_object* v_toGoalState_3001_; lean_object* v_enodeMap_3002_; lean_object* v_congrTable_3003_; lean_object* v___x_3004_; 
v___x_3000_ = lean_st_ref_get(v___y_2932_);
v_toGoalState_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc_ref(v_toGoalState_3001_);
lean_dec(v___x_3000_);
v_enodeMap_3002_ = lean_ctor_get(v_toGoalState_3001_, 1);
lean_inc_ref(v_enodeMap_3002_);
v_congrTable_3003_ = lean_ctor_get(v_toGoalState_3001_, 4);
lean_inc_ref(v_congrTable_3003_);
lean_dec_ref(v_toGoalState_3001_);
lean_inc_ref(v_self_2949_);
v___x_3004_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3002_, v_congrTable_3003_, v_self_2949_);
lean_dec_ref(v_congrTable_3003_);
lean_dec_ref(v_enodeMap_3002_);
if (lean_obj_tag(v___x_3004_) == 0)
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
goto v___jp_2970_;
}
else
{
lean_object* v_val_3005_; lean_object* v_fst_3006_; lean_object* v___x_3007_; 
v_val_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_val_3005_);
lean_dec_ref(v___x_3004_);
v_fst_3006_ = lean_ctor_get(v_val_3005_, 0);
lean_inc(v_fst_3006_);
lean_dec(v_val_3005_);
v___x_3007_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3006_, v___y_2933_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; uint8_t v___x_3009_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref(v___x_3007_);
v___x_3009_ = lean_unbox(v_a_3008_);
lean_dec(v_a_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v_toGoalState_3011_; lean_object* v_mvarId_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3086_; 
v___x_3010_ = lean_st_ref_take(v___y_2932_);
v_toGoalState_3011_ = lean_ctor_get(v___x_3010_, 0);
v_mvarId_3012_ = lean_ctor_get(v___x_3010_, 1);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3014_ = v___x_3010_;
v_isShared_3015_ = v_isSharedCheck_3086_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_mvarId_3012_);
lean_inc(v_toGoalState_3011_);
lean_dec(v___x_3010_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3086_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v_nextDeclIdx_3016_; lean_object* v_enodeMap_3017_; lean_object* v_exprs_3018_; lean_object* v_parents_3019_; lean_object* v_congrTable_3020_; lean_object* v_appMap_3021_; lean_object* v_indicesFound_3022_; lean_object* v_newFacts_3023_; uint8_t v_inconsistent_3024_; lean_object* v_nextIdx_3025_; lean_object* v_newRawFacts_3026_; lean_object* v_facts_3027_; lean_object* v_extThms_3028_; lean_object* v_ematch_3029_; lean_object* v_inj_3030_; lean_object* v_split_3031_; lean_object* v_clean_3032_; lean_object* v_sstates_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3085_; 
v_nextDeclIdx_3016_ = lean_ctor_get(v_toGoalState_3011_, 0);
v_enodeMap_3017_ = lean_ctor_get(v_toGoalState_3011_, 1);
v_exprs_3018_ = lean_ctor_get(v_toGoalState_3011_, 2);
v_parents_3019_ = lean_ctor_get(v_toGoalState_3011_, 3);
v_congrTable_3020_ = lean_ctor_get(v_toGoalState_3011_, 4);
v_appMap_3021_ = lean_ctor_get(v_toGoalState_3011_, 5);
v_indicesFound_3022_ = lean_ctor_get(v_toGoalState_3011_, 6);
v_newFacts_3023_ = lean_ctor_get(v_toGoalState_3011_, 7);
v_inconsistent_3024_ = lean_ctor_get_uint8(v_toGoalState_3011_, sizeof(void*)*17);
v_nextIdx_3025_ = lean_ctor_get(v_toGoalState_3011_, 8);
v_newRawFacts_3026_ = lean_ctor_get(v_toGoalState_3011_, 9);
v_facts_3027_ = lean_ctor_get(v_toGoalState_3011_, 10);
v_extThms_3028_ = lean_ctor_get(v_toGoalState_3011_, 11);
v_ematch_3029_ = lean_ctor_get(v_toGoalState_3011_, 12);
v_inj_3030_ = lean_ctor_get(v_toGoalState_3011_, 13);
v_split_3031_ = lean_ctor_get(v_toGoalState_3011_, 14);
v_clean_3032_ = lean_ctor_get(v_toGoalState_3011_, 15);
v_sstates_3033_ = lean_ctor_get(v_toGoalState_3011_, 16);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_toGoalState_3011_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3035_ = v_toGoalState_3011_;
v_isShared_3036_ = v_isSharedCheck_3085_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_sstates_3033_);
lean_inc(v_clean_3032_);
lean_inc(v_split_3031_);
lean_inc(v_inj_3030_);
lean_inc(v_ematch_3029_);
lean_inc(v_extThms_3028_);
lean_inc(v_facts_3027_);
lean_inc(v_newRawFacts_3026_);
lean_inc(v_nextIdx_3025_);
lean_inc(v_newFacts_3023_);
lean_inc(v_indicesFound_3022_);
lean_inc(v_appMap_3021_);
lean_inc(v_congrTable_3020_);
lean_inc(v_parents_3019_);
lean_inc(v_exprs_3018_);
lean_inc(v_enodeMap_3017_);
lean_inc(v_nextDeclIdx_3016_);
lean_dec(v_toGoalState_3011_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3085_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3037_ = lean_box(0);
lean_inc_ref(v_self_2949_);
v___x_3038_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3017_, v_congrTable_3020_, v_self_2949_, v___x_3037_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 4, v___x_3038_);
v___x_3040_ = v___x_3035_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_nextDeclIdx_3016_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_enodeMap_3017_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_exprs_3018_);
lean_ctor_set(v_reuseFailAlloc_3084_, 3, v_parents_3019_);
lean_ctor_set(v_reuseFailAlloc_3084_, 4, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3084_, 5, v_appMap_3021_);
lean_ctor_set(v_reuseFailAlloc_3084_, 6, v_indicesFound_3022_);
lean_ctor_set(v_reuseFailAlloc_3084_, 7, v_newFacts_3023_);
lean_ctor_set(v_reuseFailAlloc_3084_, 8, v_nextIdx_3025_);
lean_ctor_set(v_reuseFailAlloc_3084_, 9, v_newRawFacts_3026_);
lean_ctor_set(v_reuseFailAlloc_3084_, 10, v_facts_3027_);
lean_ctor_set(v_reuseFailAlloc_3084_, 11, v_extThms_3028_);
lean_ctor_set(v_reuseFailAlloc_3084_, 12, v_ematch_3029_);
lean_ctor_set(v_reuseFailAlloc_3084_, 13, v_inj_3030_);
lean_ctor_set(v_reuseFailAlloc_3084_, 14, v_split_3031_);
lean_ctor_set(v_reuseFailAlloc_3084_, 15, v_clean_3032_);
lean_ctor_set(v_reuseFailAlloc_3084_, 16, v_sstates_3033_);
lean_ctor_set_uint8(v_reuseFailAlloc_3084_, sizeof(void*)*17, v_inconsistent_3024_);
v___x_3040_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3040_);
v___x_3042_ = v___x_3014_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_mvarId_3012_);
v___x_3042_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = lean_st_ref_set(v___y_2932_, v___x_3042_);
lean_inc_ref(v_rootNew_2929_);
lean_inc_ref(v_next_2950_);
lean_inc_ref_n(v_self_2949_, 3);
v___x_3044_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3044_, 0, v_self_2949_);
lean_ctor_set(v___x_3044_, 1, v_next_2950_);
lean_ctor_set(v___x_3044_, 2, v_rootNew_2929_);
lean_ctor_set(v___x_3044_, 3, v_self_2949_);
lean_ctor_set(v___x_3044_, 4, v_target_x3f_2952_);
lean_ctor_set(v___x_3044_, 5, v_proof_x3f_2953_);
lean_ctor_set(v___x_3044_, 6, v_size_2955_);
lean_ctor_set(v___x_3044_, 7, v_idx_2960_);
lean_ctor_set(v___x_3044_, 8, v_generation_2961_);
lean_ctor_set(v___x_3044_, 9, v_mt_2962_);
lean_ctor_set(v___x_3044_, 10, v_sTerms_2963_);
lean_ctor_set(v___x_3044_, 11, v_ematchDiagSource_2965_);
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*12, v_flipped_2954_);
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*12 + 1, v_interpreted_2956_);
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*12 + 2, v_ctor_2957_);
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*12 + 3, v_hasLambdas_2958_);
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*12 + 4, v_heqProofs_2959_);
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*12 + 5, v_funCC_2964_);
v___x_3045_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2949_, v___x_3044_, v___y_2932_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
lean_dec_ref(v___x_3045_);
v___x_3046_ = lean_st_ref_get(v___y_2932_);
lean_inc(v_fst_3006_);
v___x_3047_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3046_, v_fst_3006_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___x_3046_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v_self_3049_; lean_object* v_next_3050_; lean_object* v_root_3051_; lean_object* v_target_x3f_3052_; lean_object* v_proof_x3f_3053_; uint8_t v_flipped_3054_; lean_object* v_size_3055_; uint8_t v_interpreted_3056_; uint8_t v_ctor_3057_; uint8_t v_hasLambdas_3058_; uint8_t v_heqProofs_3059_; lean_object* v_idx_3060_; lean_object* v_generation_3061_; lean_object* v_mt_3062_; lean_object* v_sTerms_3063_; uint8_t v_funCC_3064_; lean_object* v_ematchDiagSource_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3073_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v_self_3049_ = lean_ctor_get(v_a_3048_, 0);
v_next_3050_ = lean_ctor_get(v_a_3048_, 1);
v_root_3051_ = lean_ctor_get(v_a_3048_, 2);
v_target_x3f_3052_ = lean_ctor_get(v_a_3048_, 4);
v_proof_x3f_3053_ = lean_ctor_get(v_a_3048_, 5);
v_flipped_3054_ = lean_ctor_get_uint8(v_a_3048_, sizeof(void*)*12);
v_size_3055_ = lean_ctor_get(v_a_3048_, 6);
v_interpreted_3056_ = lean_ctor_get_uint8(v_a_3048_, sizeof(void*)*12 + 1);
v_ctor_3057_ = lean_ctor_get_uint8(v_a_3048_, sizeof(void*)*12 + 2);
v_hasLambdas_3058_ = lean_ctor_get_uint8(v_a_3048_, sizeof(void*)*12 + 3);
v_heqProofs_3059_ = lean_ctor_get_uint8(v_a_3048_, sizeof(void*)*12 + 4);
v_idx_3060_ = lean_ctor_get(v_a_3048_, 7);
v_generation_3061_ = lean_ctor_get(v_a_3048_, 8);
v_mt_3062_ = lean_ctor_get(v_a_3048_, 9);
v_sTerms_3063_ = lean_ctor_get(v_a_3048_, 10);
v_funCC_3064_ = lean_ctor_get_uint8(v_a_3048_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3065_ = lean_ctor_get(v_a_3048_, 11);
v_isSharedCheck_3073_ = !lean_is_exclusive(v_a_3048_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v_a_3048_, 3);
lean_dec(v_unused_3074_);
v___x_3067_ = v_a_3048_;
v_isShared_3068_ = v_isSharedCheck_3073_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_ematchDiagSource_3065_);
lean_inc(v_sTerms_3063_);
lean_inc(v_mt_3062_);
lean_inc(v_generation_3061_);
lean_inc(v_idx_3060_);
lean_inc(v_size_3055_);
lean_inc(v_proof_x3f_3053_);
lean_inc(v_target_x3f_3052_);
lean_inc(v_root_3051_);
lean_inc(v_next_3050_);
lean_inc(v_self_3049_);
lean_dec(v_a_3048_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3073_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 3, v_self_2949_);
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_self_3049_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_next_3050_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_root_3051_);
lean_ctor_set(v_reuseFailAlloc_3072_, 3, v_self_2949_);
lean_ctor_set(v_reuseFailAlloc_3072_, 4, v_target_x3f_3052_);
lean_ctor_set(v_reuseFailAlloc_3072_, 5, v_proof_x3f_3053_);
lean_ctor_set(v_reuseFailAlloc_3072_, 6, v_size_3055_);
lean_ctor_set(v_reuseFailAlloc_3072_, 7, v_idx_3060_);
lean_ctor_set(v_reuseFailAlloc_3072_, 8, v_generation_3061_);
lean_ctor_set(v_reuseFailAlloc_3072_, 9, v_mt_3062_);
lean_ctor_set(v_reuseFailAlloc_3072_, 10, v_sTerms_3063_);
lean_ctor_set(v_reuseFailAlloc_3072_, 11, v_ematchDiagSource_3065_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12, v_flipped_3054_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12 + 1, v_interpreted_3056_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12 + 2, v_ctor_3057_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12 + 3, v_hasLambdas_3058_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12 + 4, v_heqProofs_3059_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, sizeof(void*)*12 + 5, v_funCC_3064_);
v___x_3070_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3006_, v___x_3070_, v___y_2932_);
v___y_2984_ = v___x_3071_;
goto v___jp_2983_;
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_fst_3006_);
lean_dec_ref(v_next_2950_);
lean_dec_ref(v_self_2949_);
lean_del_object(v___x_2947_);
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2929_);
v_a_3075_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3047_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3047_);
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
lean_dec(v_fst_3006_);
lean_dec_ref(v_self_2949_);
v___y_2984_ = v___x_3045_;
goto v___jp_2983_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3006_);
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_self_2949_);
goto v___jp_2970_;
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_fst_3006_);
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
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2929_);
v_a_3087_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3007_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3007_);
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
goto v___jp_2970_;
}
}
}
}
else
{
lean_dec_ref(v___x_2994_);
lean_dec(v_ematchDiagSource_2965_);
lean_dec(v_sTerms_2963_);
lean_dec(v_mt_2962_);
lean_dec(v_generation_2961_);
lean_dec(v_idx_2960_);
lean_dec(v_size_2955_);
lean_dec(v_proof_x3f_2953_);
lean_dec(v_target_x3f_2952_);
lean_dec_ref(v_self_2949_);
v___y_2984_ = v___x_2995_;
goto v___jp_2983_;
}
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2929_);
v_a_3099_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_2944_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_2944_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3109_, lean_object* v_rootNew_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
uint8_t v_a_27974__boxed_3120_; lean_object* v_res_3121_; 
v_a_27974__boxed_3120_ = lean_unbox(v_a_3111_);
v_res_3121_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3109_, v_rootNew_3110_, v_a_27974__boxed_3120_, v_a_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v_lhs_3109_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3122_, lean_object* v_rootNew_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3123_, v_a_3128_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref(v___x_3135_);
v___x_3137_ = lean_box(0);
lean_inc_ref(v_lhs_3122_);
v___x_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
lean_ctor_set(v___x_3138_, 1, v_lhs_3122_);
v___x_3139_ = lean_unbox(v_a_3136_);
lean_dec(v_a_3136_);
v___x_3140_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3122_, v_rootNew_3123_, v___x_3139_, v___x_3138_, v_a_3124_, v_a_3128_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
lean_dec_ref(v_lhs_3122_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3154_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3143_ = v___x_3140_;
v_isShared_3144_ = v_isSharedCheck_3154_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3154_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v_fst_3145_; 
v_fst_3145_ = lean_ctor_get(v_a_3141_, 0);
lean_inc(v_fst_3145_);
lean_dec(v_a_3141_);
if (lean_obj_tag(v_fst_3145_) == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3148_; 
v___x_3146_ = lean_box(0);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 0, v___x_3146_);
v___x_3148_ = v___x_3143_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3146_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
else
{
lean_object* v_val_3150_; lean_object* v___x_3152_; 
v_val_3150_ = lean_ctor_get(v_fst_3145_, 0);
lean_inc(v_val_3150_);
lean_dec_ref(v_fst_3145_);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 0, v_val_3150_);
v___x_3152_ = v___x_3143_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_val_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
v_a_3155_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3140_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3140_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref(v_rootNew_3123_);
lean_dec_ref(v_lhs_3122_);
v_a_3163_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3135_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3135_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3171_, lean_object* v_rootNew_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3171_, v_rootNew_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_a_3174_);
lean_dec(v_a_3173_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3185_, lean_object* v_00_u03b2_3186_, lean_object* v_x_3187_, lean_object* v_x_3188_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3185_, v_x_3187_, v_x_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3190_, lean_object* v_00_u03b2_3191_, lean_object* v_x_3192_, lean_object* v_x_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3190_, v_00_u03b2_3191_, v_x_3192_, v_x_3193_);
lean_dec_ref(v_x_3192_);
lean_dec_ref(v___x_3190_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3195_, lean_object* v_00_u03b2_3196_, lean_object* v_x_3197_, lean_object* v_x_3198_, lean_object* v_x_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3195_, v_x_3197_, v_x_3198_, v_x_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3201_, lean_object* v_00_u03b2_3202_, lean_object* v_x_3203_, lean_object* v_x_3204_, lean_object* v_x_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3201_, v_00_u03b2_3202_, v_x_3203_, v_x_3204_, v_x_3205_);
lean_dec_ref(v___x_3201_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3207_, lean_object* v_rootNew_3208_, uint8_t v_a_3209_, lean_object* v_inst_3210_, lean_object* v_a_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3207_, v_rootNew_3208_, v_a_3209_, v_a_3211_, v___y_3212_, v___y_3216_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3224_, lean_object* v_rootNew_3225_, lean_object* v_a_3226_, lean_object* v_inst_3227_, lean_object* v_a_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
uint8_t v_a_28329__boxed_3240_; lean_object* v_res_3241_; 
v_a_28329__boxed_3240_ = lean_unbox(v_a_3226_);
v_res_3241_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3224_, v_rootNew_3225_, v_a_28329__boxed_3240_, v_inst_3227_, v_a_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v_lhs_3224_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3242_, lean_object* v_00_u03b2_3243_, lean_object* v_x_3244_, size_t v_x_3245_, lean_object* v_x_3246_){
_start:
{
lean_object* v___x_3247_; 
lean_inc_ref(v_x_3244_);
v___x_3247_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3242_, v_x_3244_, v_x_3245_, v_x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3248_, lean_object* v_00_u03b2_3249_, lean_object* v_x_3250_, lean_object* v_x_3251_, lean_object* v_x_3252_){
_start:
{
size_t v_x_28372__boxed_3253_; lean_object* v_res_3254_; 
v_x_28372__boxed_3253_ = lean_unbox_usize(v_x_3251_);
lean_dec(v_x_3251_);
v_res_3254_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3248_, v_00_u03b2_3249_, v_x_3250_, v_x_28372__boxed_3253_, v_x_3252_);
lean_dec_ref(v_x_3250_);
lean_dec_ref(v___x_3248_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3255_, lean_object* v_00_u03b2_3256_, lean_object* v_x_3257_, size_t v_x_3258_, size_t v_x_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_){
_start:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3255_, v_x_3257_, v_x_3258_, v_x_3259_, v_x_3260_, v_x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3263_, lean_object* v_00_u03b2_3264_, lean_object* v_x_3265_, lean_object* v_x_3266_, lean_object* v_x_3267_, lean_object* v_x_3268_, lean_object* v_x_3269_){
_start:
{
size_t v_x_28386__boxed_3270_; size_t v_x_28387__boxed_3271_; lean_object* v_res_3272_; 
v_x_28386__boxed_3270_ = lean_unbox_usize(v_x_3266_);
lean_dec(v_x_3266_);
v_x_28387__boxed_3271_ = lean_unbox_usize(v_x_3267_);
lean_dec(v_x_3267_);
v_res_3272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3263_, v_00_u03b2_3264_, v_x_3265_, v_x_28386__boxed_3270_, v_x_28387__boxed_3271_, v_x_3268_, v_x_3269_);
lean_dec_ref(v___x_3263_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3273_, lean_object* v_00_u03b2_3274_, lean_object* v_keys_3275_, lean_object* v_vals_3276_, lean_object* v_heq_3277_, lean_object* v_i_3278_, lean_object* v_k_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3273_, v_keys_3275_, v_vals_3276_, v_i_3278_, v_k_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3281_, lean_object* v_00_u03b2_3282_, lean_object* v_keys_3283_, lean_object* v_vals_3284_, lean_object* v_heq_3285_, lean_object* v_i_3286_, lean_object* v_k_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3281_, v_00_u03b2_3282_, v_keys_3283_, v_vals_3284_, v_heq_3285_, v_i_3286_, v_k_3287_);
lean_dec_ref(v_vals_3284_);
lean_dec_ref(v_keys_3283_);
lean_dec_ref(v___x_3281_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3289_, lean_object* v_00_u03b2_3290_, lean_object* v_n_3291_, lean_object* v_k_3292_, lean_object* v_v_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3289_, v_n_3291_, v_k_3292_, v_v_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3295_, lean_object* v_00_u03b2_3296_, lean_object* v_n_3297_, lean_object* v_k_3298_, lean_object* v_v_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3295_, v_00_u03b2_3296_, v_n_3297_, v_k_3298_, v_v_3299_);
lean_dec_ref(v___x_3295_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3301_, lean_object* v_00_u03b2_3302_, size_t v_depth_3303_, lean_object* v_keys_3304_, lean_object* v_vals_3305_, lean_object* v_heq_3306_, lean_object* v_i_3307_, lean_object* v_entries_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3301_, v_depth_3303_, v_keys_3304_, v_vals_3305_, v_i_3307_, v_entries_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3310_, lean_object* v_00_u03b2_3311_, lean_object* v_depth_3312_, lean_object* v_keys_3313_, lean_object* v_vals_3314_, lean_object* v_heq_3315_, lean_object* v_i_3316_, lean_object* v_entries_3317_){
_start:
{
size_t v_depth_boxed_3318_; lean_object* v_res_3319_; 
v_depth_boxed_3318_ = lean_unbox_usize(v_depth_3312_);
lean_dec(v_depth_3312_);
v_res_3319_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3310_, v_00_u03b2_3311_, v_depth_boxed_3318_, v_keys_3313_, v_vals_3314_, v_heq_3315_, v_i_3316_, v_entries_3317_);
lean_dec_ref(v_vals_3314_);
lean_dec_ref(v_keys_3313_);
lean_dec_ref(v___x_3310_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3320_, lean_object* v_00_u03b2_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_, lean_object* v_x_3324_, lean_object* v_x_3325_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3320_, v_x_3322_, v_x_3323_, v_x_3324_, v_x_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3327_, lean_object* v_00_u03b2_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_, lean_object* v_x_3331_, lean_object* v_x_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3327_, v_00_u03b2_3328_, v_x_3329_, v_x_3330_, v_x_3331_, v_x_3332_);
lean_dec_ref(v___x_3327_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3334_, lean_object* v_b_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
if (lean_obj_tag(v_as_x27_3334_) == 0)
{
lean_object* v___x_3347_; 
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_b_3335_);
return v___x_3347_;
}
else
{
lean_object* v_head_3348_; lean_object* v_tail_3349_; lean_object* v___x_3350_; 
v_head_3348_ = lean_ctor_get(v_as_x27_3334_, 0);
v_tail_3349_ = lean_ctor_get(v_as_x27_3334_, 1);
lean_inc(v_head_3348_);
v___x_3350_ = l_Lean_Meta_Grind_propagateUp(v_head_3348_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v___x_3351_; 
lean_dec_ref(v___x_3350_);
v___x_3351_ = lean_box(0);
v_as_x27_3334_ = v_tail_3349_;
v_b_3335_ = v___x_3351_;
goto _start;
}
else
{
return v___x_3350_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3353_, lean_object* v_b_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3353_, v_b_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v_as_x27_3353_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3367_, lean_object* v_b_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
if (lean_obj_tag(v_as_x27_3367_) == 0)
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v_b_3368_);
return v___x_3380_;
}
else
{
lean_object* v_head_3381_; lean_object* v_tail_3382_; lean_object* v___x_3383_; 
v_head_3381_ = lean_ctor_get(v_as_x27_3367_, 0);
v_tail_3382_ = lean_ctor_get(v_as_x27_3367_, 1);
lean_inc(v_head_3381_);
v___x_3383_ = l_Lean_Meta_Grind_propagateDown(v_head_3381_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3384_; 
lean_dec_ref(v___x_3383_);
v___x_3384_ = lean_box(0);
v_as_x27_3367_ = v_tail_3382_;
v_b_3368_ = v___x_3384_;
goto _start;
}
else
{
return v___x_3383_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3386_, lean_object* v_b_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3386_, v_b_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec(v_as_x27_3386_);
return v_res_3399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v_cls_3403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3404_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3405_ = l_Lean_Name_append(v___x_3404_, v_cls_3403_);
return v___x_3405_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3408_ = l_Lean_stringToMessageData(v___x_3407_);
return v___x_3408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3411_ = l_Lean_stringToMessageData(v___x_3410_);
return v___x_3411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3414_ = l_Lean_stringToMessageData(v___x_3413_);
return v___x_3414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3417_ = l_Lean_stringToMessageData(v___x_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3418_, uint8_t v_isHEq_3419_, lean_object* v_lhs_3420_, lean_object* v_rhs_3421_, lean_object* v_lhsNode_3422_, lean_object* v_rhsNode_3423_, lean_object* v_lhsRoot_3424_, lean_object* v_rhsRoot_3425_, uint8_t v_flipped_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; uint8_t v___y_3494_; uint8_t v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; uint8_t v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; uint8_t v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; uint8_t v___y_3525_; uint8_t v___y_3526_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; uint8_t v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; uint8_t v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; uint8_t v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; uint8_t v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; uint8_t v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; uint8_t v___y_3591_; uint8_t v___y_3592_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; uint8_t v___y_3603_; uint8_t v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v_options_3676_; lean_object* v_inheritedTraceOptions_3677_; uint8_t v_hasTrace_3678_; lean_object* v_cls_3679_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v_fns_u2082_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v_fns_u2081_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; 
v_options_3676_ = lean_ctor_get(v_a_3435_, 2);
v_inheritedTraceOptions_3677_ = lean_ctor_get(v_a_3435_, 13);
v_hasTrace_3678_ = lean_ctor_get_uint8(v_options_3676_, sizeof(void*)*1);
v_cls_3679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3678_ == 0)
{
v___y_3798_ = v_a_3427_;
v___y_3799_ = v_a_3428_;
v___y_3800_ = v_a_3429_;
v___y_3801_ = v_a_3430_;
v___y_3802_ = v_a_3431_;
v___y_3803_ = v_a_3432_;
v___y_3804_ = v_a_3433_;
v___y_3805_ = v_a_3434_;
v___y_3806_ = v_a_3435_;
v___y_3807_ = v_a_3436_;
goto v___jp_3797_;
}
else
{
lean_object* v___x_3878_; uint8_t v___x_3879_; 
v___x_3878_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3879_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3677_, v_options_3676_, v___x_3878_);
if (v___x_3879_ == 0)
{
v___y_3798_ = v_a_3427_;
v___y_3799_ = v_a_3428_;
v___y_3800_ = v_a_3429_;
v___y_3801_ = v_a_3430_;
v___y_3802_ = v_a_3431_;
v___y_3803_ = v_a_3432_;
v___y_3804_ = v_a_3433_;
v___y_3805_ = v_a_3434_;
v___y_3806_ = v_a_3435_;
v___y_3807_ = v_a_3436_;
goto v___jp_3797_;
}
else
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Lean_Meta_Grind_updateLastTag(v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v___x_3881_; 
lean_dec_ref(v___x_3880_);
lean_inc_ref(v_lhs_3420_);
v___x_3881_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3420_, v_a_3427_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3883_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref(v___x_3881_);
lean_inc_ref(v_rhs_3421_);
v___x_3883_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3421_, v_a_3427_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref(v___x_3883_);
v___x_3885_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
lean_ctor_set(v___x_3886_, 1, v_a_3882_);
v___x_3887_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3886_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
lean_ctor_set(v___x_3889_, 1, v_a_3884_);
v___x_3890_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3679_, v___x_3889_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_dec_ref(v___x_3890_);
v___y_3798_ = v_a_3427_;
v___y_3799_ = v_a_3428_;
v___y_3800_ = v_a_3429_;
v___y_3801_ = v_a_3430_;
v___y_3802_ = v_a_3431_;
v___y_3803_ = v_a_3432_;
v___y_3804_ = v_a_3433_;
v___y_3805_ = v_a_3434_;
v___y_3806_ = v_a_3435_;
v___y_3807_ = v_a_3436_;
goto v___jp_3797_;
}
else
{
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhsNode_3422_);
lean_dec_ref(v_rhs_3421_);
lean_dec_ref(v_lhs_3420_);
lean_dec_ref(v_proof_3418_);
return v___x_3890_;
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v_a_3882_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhsNode_3422_);
lean_dec_ref(v_rhs_3421_);
lean_dec_ref(v_lhs_3420_);
lean_dec_ref(v_proof_3418_);
v_a_3891_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3883_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3883_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhsNode_3422_);
lean_dec_ref(v_rhs_3421_);
lean_dec_ref(v_lhs_3420_);
lean_dec_ref(v_proof_3418_);
v_a_3899_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3881_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3881_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhsNode_3422_);
lean_dec_ref(v_rhs_3421_);
lean_dec_ref(v_lhs_3420_);
lean_dec_ref(v_proof_3418_);
return v___x_3880_;
}
}
}
v___jp_3438_:
{
lean_object* v___x_3455_; 
v___x_3455_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3445_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3481_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3481_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3481_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
uint8_t v___x_3460_; 
v___x_3460_ = lean_unbox(v_a_3456_);
lean_dec(v_a_3456_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
lean_del_object(v___x_3458_);
v___x_3461_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3441_);
lean_dec(v___y_3441_);
v___x_3462_ = lean_box(0);
v___x_3463_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3461_, v___x_3462_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___x_3461_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v___x_3464_; 
lean_dec_ref(v___x_3463_);
v___x_3464_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3440_, v___x_3462_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v___x_3465_; 
lean_dec_ref(v___x_3464_);
v___x_3465_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3444_, v___y_3443_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec_ref(v___y_3443_);
lean_dec_ref(v___y_3444_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v___x_3466_; 
lean_dec_ref(v___x_3465_);
v___x_3466_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3442_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3475_; 
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v___x_3466_, 0);
lean_dec(v_unused_3476_);
v___x_3468_ = v___x_3466_;
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
else
{
lean_dec(v___x_3466_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
uint8_t v___x_3470_; 
v___x_3470_ = l_Lean_Expr_isTrue(v___y_3439_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3472_; 
lean_dec(v___y_3440_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 0, v___x_3462_);
v___x_3472_ = v___x_3468_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3462_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
else
{
lean_object* v___x_3474_; 
lean_del_object(v___x_3468_);
v___x_3474_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3440_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3440_);
return v___x_3474_;
}
}
}
else
{
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v___x_3466_;
}
}
else
{
lean_dec(v___y_3442_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v___x_3465_;
}
}
else
{
lean_dec_ref(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v___x_3464_;
}
}
else
{
lean_dec_ref(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v___x_3463_;
}
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3479_; 
lean_dec_ref(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
v___x_3477_ = lean_box(0);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3477_);
v___x_3479_ = v___x_3458_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
v_a_3482_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3455_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3455_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
v___jp_3490_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_inc_ref(v___y_3524_);
v___x_3527_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3527_, 0, v___y_3524_);
lean_ctor_set(v___x_3527_, 1, v___y_3493_);
lean_ctor_set(v___x_3527_, 2, v___y_3502_);
lean_ctor_set(v___x_3527_, 3, v___y_3511_);
lean_ctor_set(v___x_3527_, 4, v___y_3508_);
lean_ctor_set(v___x_3527_, 5, v___y_3520_);
lean_ctor_set(v___x_3527_, 6, v___y_3504_);
lean_ctor_set(v___x_3527_, 7, v___y_3505_);
lean_ctor_set(v___x_3527_, 8, v___y_3510_);
lean_ctor_set(v___x_3527_, 9, v___y_3512_);
lean_ctor_set(v___x_3527_, 10, v___y_3523_);
lean_ctor_set(v___x_3527_, 11, v___y_3497_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*12, v___y_3495_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*12 + 1, v___y_3522_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*12 + 2, v___y_3517_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*12 + 3, v___y_3494_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*12 + 4, v___y_3526_);
lean_ctor_set_uint8(v___x_3527_, sizeof(void*)*12 + 5, v___y_3525_);
lean_inc_ref(v___y_3513_);
v___x_3528_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3513_, v___x_3527_, v___y_3518_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v___x_3529_; 
lean_dec_ref(v___x_3528_);
lean_inc_ref(v___y_3516_);
v___x_3529_ = l_Lean_Meta_Grind_propagateBeta(v___y_3516_, v___y_3503_, v___y_3518_, v___y_3498_, v___y_3506_, v___y_3496_, v___y_3501_, v___y_3521_, v___y_3492_, v___y_3507_, v___y_3491_, v___y_3499_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v___x_3530_; 
lean_dec_ref(v___x_3529_);
lean_inc_ref(v___y_3509_);
v___x_3530_ = l_Lean_Meta_Grind_propagateBeta(v___y_3509_, v___y_3519_, v___y_3518_, v___y_3498_, v___y_3506_, v___y_3496_, v___y_3501_, v___y_3521_, v___y_3492_, v___y_3507_, v___y_3491_, v___y_3499_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v___x_3531_; 
lean_dec_ref(v___x_3530_);
v___x_3531_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3425_, v_lhsRoot_3424_, v___y_3518_, v___y_3492_, v___y_3507_, v___y_3491_, v___y_3499_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref(v___x_3531_);
v___x_3533_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3514_, v___y_3518_);
lean_dec_ref(v___y_3514_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v___x_3534_; 
lean_dec_ref(v___x_3533_);
lean_inc_ref(v___y_3513_);
v___x_3534_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3500_, v___y_3513_, v___y_3518_, v___y_3498_, v___y_3506_, v___y_3496_, v___y_3501_, v___y_3521_, v___y_3492_, v___y_3507_, v___y_3491_, v___y_3499_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v___x_3535_; 
lean_dec_ref(v___x_3534_);
v___x_3535_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3518_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; uint8_t v___x_3537_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref(v___x_3535_);
v___x_3537_ = lean_unbox(v_a_3536_);
lean_dec(v_a_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; 
v___x_3538_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3524_, v___y_3518_, v___y_3498_, v___y_3506_, v___y_3496_, v___y_3501_, v___y_3521_, v___y_3492_, v___y_3507_, v___y_3491_, v___y_3499_);
lean_dec_ref(v___y_3524_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_dec_ref(v___x_3538_);
v___y_3439_ = v___y_3513_;
v___y_3440_ = v___y_3515_;
v___y_3441_ = v___y_3500_;
v___y_3442_ = v_a_3532_;
v___y_3443_ = v___y_3509_;
v___y_3444_ = v___y_3516_;
v___y_3445_ = v___y_3518_;
v___y_3446_ = v___y_3498_;
v___y_3447_ = v___y_3506_;
v___y_3448_ = v___y_3496_;
v___y_3449_ = v___y_3501_;
v___y_3450_ = v___y_3521_;
v___y_3451_ = v___y_3492_;
v___y_3452_ = v___y_3507_;
v___y_3453_ = v___y_3491_;
v___y_3454_ = v___y_3499_;
goto v___jp_3438_;
}
else
{
lean_dec(v_a_3532_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3500_);
return v___x_3538_;
}
}
else
{
lean_dec_ref(v___y_3524_);
v___y_3439_ = v___y_3513_;
v___y_3440_ = v___y_3515_;
v___y_3441_ = v___y_3500_;
v___y_3442_ = v_a_3532_;
v___y_3443_ = v___y_3509_;
v___y_3444_ = v___y_3516_;
v___y_3445_ = v___y_3518_;
v___y_3446_ = v___y_3498_;
v___y_3447_ = v___y_3506_;
v___y_3448_ = v___y_3496_;
v___y_3449_ = v___y_3501_;
v___y_3450_ = v___y_3521_;
v___y_3451_ = v___y_3492_;
v___y_3452_ = v___y_3507_;
v___y_3453_ = v___y_3491_;
v___y_3454_ = v___y_3499_;
goto v___jp_3438_;
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_a_3532_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3500_);
v_a_3539_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3535_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3535_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
else
{
lean_dec(v_a_3532_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3500_);
return v___x_3534_;
}
}
else
{
lean_dec(v_a_3532_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3500_);
return v___x_3533_;
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3500_);
v_a_3547_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3531_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3531_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
else
{
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3500_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
return v___x_3530_;
}
}
else
{
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3500_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
return v___x_3529_;
}
}
else
{
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3500_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
return v___x_3528_;
}
}
v___jp_3555_:
{
if (v_isHEq_3419_ == 0)
{
if (v___y_3576_ == 0)
{
v___y_3491_ = v___y_3558_;
v___y_3492_ = v___y_3557_;
v___y_3493_ = v___y_3556_;
v___y_3494_ = v___y_3592_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3559_;
v___y_3497_ = v___y_3562_;
v___y_3498_ = v___y_3561_;
v___y_3499_ = v___y_3563_;
v___y_3500_ = v___y_3566_;
v___y_3501_ = v___y_3565_;
v___y_3502_ = v___y_3564_;
v___y_3503_ = v___y_3567_;
v___y_3504_ = v___y_3569_;
v___y_3505_ = v___y_3570_;
v___y_3506_ = v___y_3571_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3573_;
v___y_3509_ = v___y_3574_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3577_;
v___y_3512_ = v___y_3578_;
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3580_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3586_;
v___y_3520_ = v___y_3585_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3587_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3568_;
goto v___jp_3490_;
}
else
{
v___y_3491_ = v___y_3558_;
v___y_3492_ = v___y_3557_;
v___y_3493_ = v___y_3556_;
v___y_3494_ = v___y_3592_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3559_;
v___y_3497_ = v___y_3562_;
v___y_3498_ = v___y_3561_;
v___y_3499_ = v___y_3563_;
v___y_3500_ = v___y_3566_;
v___y_3501_ = v___y_3565_;
v___y_3502_ = v___y_3564_;
v___y_3503_ = v___y_3567_;
v___y_3504_ = v___y_3569_;
v___y_3505_ = v___y_3570_;
v___y_3506_ = v___y_3571_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3573_;
v___y_3509_ = v___y_3574_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3577_;
v___y_3512_ = v___y_3578_;
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3580_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3586_;
v___y_3520_ = v___y_3585_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3587_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3576_;
goto v___jp_3490_;
}
}
else
{
v___y_3491_ = v___y_3558_;
v___y_3492_ = v___y_3557_;
v___y_3493_ = v___y_3556_;
v___y_3494_ = v___y_3592_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3559_;
v___y_3497_ = v___y_3562_;
v___y_3498_ = v___y_3561_;
v___y_3499_ = v___y_3563_;
v___y_3500_ = v___y_3566_;
v___y_3501_ = v___y_3565_;
v___y_3502_ = v___y_3564_;
v___y_3503_ = v___y_3567_;
v___y_3504_ = v___y_3569_;
v___y_3505_ = v___y_3570_;
v___y_3506_ = v___y_3571_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3573_;
v___y_3509_ = v___y_3574_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3577_;
v___y_3512_ = v___y_3578_;
v___y_3513_ = v___y_3579_;
v___y_3514_ = v___y_3580_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3586_;
v___y_3520_ = v___y_3585_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3587_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3590_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v_isHEq_3419_;
goto v___jp_3490_;
}
}
v___jp_3593_:
{
lean_object* v___x_3616_; 
v___x_3616_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3599_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
lean_dec_ref(v___x_3616_);
v___x_3617_ = lean_st_ref_get(v___y_3606_);
v___x_3618_ = lean_st_ref_get(v___y_3606_);
lean_inc_ref(v___y_3598_);
v___x_3619_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3618_, v___y_3598_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___x_3618_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; lean_object* v_self_3621_; lean_object* v_root_3622_; lean_object* v_congr_3623_; lean_object* v_target_x3f_3624_; lean_object* v_proof_x3f_3625_; uint8_t v_flipped_3626_; lean_object* v_size_3627_; uint8_t v_interpreted_3628_; uint8_t v_ctor_3629_; uint8_t v_hasLambdas_3630_; uint8_t v_heqProofs_3631_; lean_object* v_idx_3632_; lean_object* v_generation_3633_; lean_object* v_mt_3634_; lean_object* v_sTerms_3635_; uint8_t v_funCC_3636_; lean_object* v_ematchDiagSource_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3666_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
lean_dec_ref(v___x_3619_);
v_self_3621_ = lean_ctor_get(v_a_3620_, 0);
v_root_3622_ = lean_ctor_get(v_a_3620_, 2);
v_congr_3623_ = lean_ctor_get(v_a_3620_, 3);
v_target_x3f_3624_ = lean_ctor_get(v_a_3620_, 4);
v_proof_x3f_3625_ = lean_ctor_get(v_a_3620_, 5);
v_flipped_3626_ = lean_ctor_get_uint8(v_a_3620_, sizeof(void*)*12);
v_size_3627_ = lean_ctor_get(v_a_3620_, 6);
v_interpreted_3628_ = lean_ctor_get_uint8(v_a_3620_, sizeof(void*)*12 + 1);
v_ctor_3629_ = lean_ctor_get_uint8(v_a_3620_, sizeof(void*)*12 + 2);
v_hasLambdas_3630_ = lean_ctor_get_uint8(v_a_3620_, sizeof(void*)*12 + 3);
v_heqProofs_3631_ = lean_ctor_get_uint8(v_a_3620_, sizeof(void*)*12 + 4);
v_idx_3632_ = lean_ctor_get(v_a_3620_, 7);
v_generation_3633_ = lean_ctor_get(v_a_3620_, 8);
v_mt_3634_ = lean_ctor_get(v_a_3620_, 9);
v_sTerms_3635_ = lean_ctor_get(v_a_3620_, 10);
v_funCC_3636_ = lean_ctor_get_uint8(v_a_3620_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3637_ = lean_ctor_get(v_a_3620_, 11);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_a_3620_);
if (v_isSharedCheck_3666_ == 0)
{
lean_object* v_unused_3667_; 
v_unused_3667_ = lean_ctor_get(v_a_3620_, 1);
lean_dec(v_unused_3667_);
v___x_3639_ = v_a_3620_;
v_isShared_3640_ = v_isSharedCheck_3666_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_ematchDiagSource_3637_);
lean_inc(v_sTerms_3635_);
lean_inc(v_mt_3634_);
lean_inc(v_generation_3633_);
lean_inc(v_idx_3632_);
lean_inc(v_size_3627_);
lean_inc(v_proof_x3f_3625_);
lean_inc(v_target_x3f_3624_);
lean_inc(v_congr_3623_);
lean_inc(v_root_3622_);
lean_inc(v_self_3621_);
lean_dec(v_a_3620_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3666_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v_self_3641_; lean_object* v_next_3642_; lean_object* v_root_3643_; lean_object* v_congr_3644_; lean_object* v_target_x3f_3645_; lean_object* v_proof_x3f_3646_; uint8_t v_flipped_3647_; lean_object* v_size_3648_; uint8_t v_interpreted_3649_; uint8_t v_ctor_3650_; uint8_t v_hasLambdas_3651_; uint8_t v_heqProofs_3652_; lean_object* v_idx_3653_; lean_object* v_generation_3654_; lean_object* v_mt_3655_; lean_object* v_sTerms_3656_; uint8_t v_funCC_3657_; lean_object* v_ematchDiagSource_3658_; lean_object* v___x_3660_; 
v_self_3641_ = lean_ctor_get(v_rhsRoot_3425_, 0);
v_next_3642_ = lean_ctor_get(v_rhsRoot_3425_, 1);
v_root_3643_ = lean_ctor_get(v_rhsRoot_3425_, 2);
v_congr_3644_ = lean_ctor_get(v_rhsRoot_3425_, 3);
v_target_x3f_3645_ = lean_ctor_get(v_rhsRoot_3425_, 4);
v_proof_x3f_3646_ = lean_ctor_get(v_rhsRoot_3425_, 5);
v_flipped_3647_ = lean_ctor_get_uint8(v_rhsRoot_3425_, sizeof(void*)*12);
v_size_3648_ = lean_ctor_get(v_rhsRoot_3425_, 6);
v_interpreted_3649_ = lean_ctor_get_uint8(v_rhsRoot_3425_, sizeof(void*)*12 + 1);
v_ctor_3650_ = lean_ctor_get_uint8(v_rhsRoot_3425_, sizeof(void*)*12 + 2);
v_hasLambdas_3651_ = lean_ctor_get_uint8(v_rhsRoot_3425_, sizeof(void*)*12 + 3);
v_heqProofs_3652_ = lean_ctor_get_uint8(v_rhsRoot_3425_, sizeof(void*)*12 + 4);
v_idx_3653_ = lean_ctor_get(v_rhsRoot_3425_, 7);
v_generation_3654_ = lean_ctor_get(v_rhsRoot_3425_, 8);
v_mt_3655_ = lean_ctor_get(v_rhsRoot_3425_, 9);
v_sTerms_3656_ = lean_ctor_get(v_rhsRoot_3425_, 10);
v_funCC_3657_ = lean_ctor_get_uint8(v_rhsRoot_3425_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3658_ = lean_ctor_get(v_rhsRoot_3425_, 11);
lean_inc_ref(v_next_3642_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 1, v_next_3642_);
v___x_3660_ = v___x_3639_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_self_3621_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v_next_3642_);
lean_ctor_set(v_reuseFailAlloc_3665_, 2, v_root_3622_);
lean_ctor_set(v_reuseFailAlloc_3665_, 3, v_congr_3623_);
lean_ctor_set(v_reuseFailAlloc_3665_, 4, v_target_x3f_3624_);
lean_ctor_set(v_reuseFailAlloc_3665_, 5, v_proof_x3f_3625_);
lean_ctor_set(v_reuseFailAlloc_3665_, 6, v_size_3627_);
lean_ctor_set(v_reuseFailAlloc_3665_, 7, v_idx_3632_);
lean_ctor_set(v_reuseFailAlloc_3665_, 8, v_generation_3633_);
lean_ctor_set(v_reuseFailAlloc_3665_, 9, v_mt_3634_);
lean_ctor_set(v_reuseFailAlloc_3665_, 10, v_sTerms_3635_);
lean_ctor_set(v_reuseFailAlloc_3665_, 11, v_ematchDiagSource_3637_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, sizeof(void*)*12, v_flipped_3626_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, sizeof(void*)*12 + 1, v_interpreted_3628_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, sizeof(void*)*12 + 2, v_ctor_3629_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, sizeof(void*)*12 + 3, v_hasLambdas_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, sizeof(void*)*12 + 4, v_heqProofs_3631_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, sizeof(void*)*12 + 5, v_funCC_3636_);
v___x_3660_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3605_, v___x_3660_, v___y_3606_);
if (lean_obj_tag(v___x_3661_) == 0)
{
uint8_t v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
lean_dec_ref(v___x_3661_);
v___x_3662_ = 0;
v___x_3663_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3617_, v_lhs_3420_, v___x_3662_);
lean_dec(v___x_3617_);
v___x_3664_ = lean_nat_add(v_size_3648_, v___y_3594_);
lean_dec(v___y_3594_);
if (v_hasLambdas_3651_ == 0)
{
lean_inc_ref(v_self_3641_);
lean_inc(v_sTerms_3656_);
lean_inc(v_proof_x3f_3646_);
lean_inc(v_mt_3655_);
lean_inc_ref(v_congr_3644_);
lean_inc(v_generation_3654_);
lean_inc(v_target_x3f_3645_);
lean_inc(v_idx_3653_);
lean_inc_ref(v_root_3643_);
lean_inc(v_ematchDiagSource_3658_);
v___y_3556_ = v___y_3595_;
v___y_3557_ = v___y_3612_;
v___y_3558_ = v___y_3614_;
v___y_3559_ = v___y_3609_;
v___y_3560_ = v_flipped_3647_;
v___y_3561_ = v___y_3607_;
v___y_3562_ = v_ematchDiagSource_3658_;
v___y_3563_ = v___y_3615_;
v___y_3564_ = v_root_3643_;
v___y_3565_ = v___y_3610_;
v___y_3566_ = v___y_3599_;
v___y_3567_ = v___y_3602_;
v___y_3568_ = v___y_3604_;
v___y_3569_ = v___x_3664_;
v___y_3570_ = v_idx_3653_;
v___y_3571_ = v___y_3608_;
v___y_3572_ = v___y_3613_;
v___y_3573_ = v_target_x3f_3645_;
v___y_3574_ = v___y_3601_;
v___y_3575_ = v_generation_3654_;
v___y_3576_ = v_heqProofs_3652_;
v___y_3577_ = v_congr_3644_;
v___y_3578_ = v_mt_3655_;
v___y_3579_ = v___y_3596_;
v___y_3580_ = v___y_3598_;
v___y_3581_ = v___x_3663_;
v___y_3582_ = v___y_3600_;
v___y_3583_ = v_ctor_3650_;
v___y_3584_ = v___y_3606_;
v___y_3585_ = v_proof_x3f_3646_;
v___y_3586_ = v___y_3597_;
v___y_3587_ = v_interpreted_3649_;
v___y_3588_ = v___y_3611_;
v___y_3589_ = v_sTerms_3656_;
v___y_3590_ = v_self_3641_;
v___y_3591_ = v_funCC_3657_;
v___y_3592_ = v___y_3603_;
goto v___jp_3555_;
}
else
{
lean_inc_ref(v_self_3641_);
lean_inc(v_sTerms_3656_);
lean_inc(v_proof_x3f_3646_);
lean_inc(v_mt_3655_);
lean_inc_ref(v_congr_3644_);
lean_inc(v_generation_3654_);
lean_inc(v_target_x3f_3645_);
lean_inc(v_idx_3653_);
lean_inc_ref(v_root_3643_);
lean_inc(v_ematchDiagSource_3658_);
v___y_3556_ = v___y_3595_;
v___y_3557_ = v___y_3612_;
v___y_3558_ = v___y_3614_;
v___y_3559_ = v___y_3609_;
v___y_3560_ = v_flipped_3647_;
v___y_3561_ = v___y_3607_;
v___y_3562_ = v_ematchDiagSource_3658_;
v___y_3563_ = v___y_3615_;
v___y_3564_ = v_root_3643_;
v___y_3565_ = v___y_3610_;
v___y_3566_ = v___y_3599_;
v___y_3567_ = v___y_3602_;
v___y_3568_ = v___y_3604_;
v___y_3569_ = v___x_3664_;
v___y_3570_ = v_idx_3653_;
v___y_3571_ = v___y_3608_;
v___y_3572_ = v___y_3613_;
v___y_3573_ = v_target_x3f_3645_;
v___y_3574_ = v___y_3601_;
v___y_3575_ = v_generation_3654_;
v___y_3576_ = v_heqProofs_3652_;
v___y_3577_ = v_congr_3644_;
v___y_3578_ = v_mt_3655_;
v___y_3579_ = v___y_3596_;
v___y_3580_ = v___y_3598_;
v___y_3581_ = v___x_3663_;
v___y_3582_ = v___y_3600_;
v___y_3583_ = v_ctor_3650_;
v___y_3584_ = v___y_3606_;
v___y_3585_ = v_proof_x3f_3646_;
v___y_3586_ = v___y_3597_;
v___y_3587_ = v_interpreted_3649_;
v___y_3588_ = v___y_3611_;
v___y_3589_ = v_sTerms_3656_;
v___y_3590_ = v_self_3641_;
v___y_3591_ = v_funCC_3657_;
v___y_3592_ = v_hasLambdas_3651_;
goto v___jp_3555_;
}
}
else
{
lean_dec(v___x_3617_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_lhs_3420_);
return v___x_3661_;
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec(v___x_3617_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_lhs_3420_);
v_a_3668_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3619_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3619_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_lhs_3420_);
return v___x_3616_;
}
}
v___jp_3680_:
{
lean_object* v_self_3696_; lean_object* v_next_3697_; lean_object* v_size_3698_; uint8_t v_hasLambdas_3699_; uint8_t v_heqProofs_3700_; lean_object* v___x_3701_; 
v_self_3696_ = lean_ctor_get(v_lhsRoot_3424_, 0);
v_next_3697_ = lean_ctor_get(v_lhsRoot_3424_, 1);
v_size_3698_ = lean_ctor_get(v_lhsRoot_3424_, 6);
v_hasLambdas_3699_ = lean_ctor_get_uint8(v_lhsRoot_3424_, sizeof(void*)*12 + 3);
v_heqProofs_3700_ = lean_ctor_get_uint8(v_lhsRoot_3424_, sizeof(void*)*12 + 4);
v___x_3701_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3696_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v_root_3703_; lean_object* v___x_3704_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref(v___x_3701_);
v_root_3703_ = lean_ctor_get(v_rhsNode_3423_, 2);
lean_inc_ref_n(v_root_3703_, 2);
lean_dec_ref(v_rhsNode_3423_);
lean_inc_ref(v_lhs_3420_);
v___x_3704_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3420_, v_root_3703_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_options_3705_; uint8_t v_hasTrace_3706_; 
lean_dec_ref(v___x_3704_);
v_options_3705_ = lean_ctor_get(v___y_3694_, 2);
v_hasTrace_3706_ = lean_ctor_get_uint8(v_options_3705_, sizeof(void*)*1);
if (v_hasTrace_3706_ == 0)
{
lean_inc_ref(v_self_3696_);
lean_inc_ref(v_next_3697_);
lean_inc(v_size_3698_);
v___y_3594_ = v_size_3698_;
v___y_3595_ = v_next_3697_;
v___y_3596_ = v_root_3703_;
v___y_3597_ = v_fns_u2082_3685_;
v___y_3598_ = v_self_3696_;
v___y_3599_ = v_a_3702_;
v___y_3600_ = v___y_3682_;
v___y_3601_ = v___y_3681_;
v___y_3602_ = v___y_3683_;
v___y_3603_ = v_hasLambdas_3699_;
v___y_3604_ = v_heqProofs_3700_;
v___y_3605_ = v___y_3684_;
v___y_3606_ = v___y_3686_;
v___y_3607_ = v___y_3687_;
v___y_3608_ = v___y_3688_;
v___y_3609_ = v___y_3689_;
v___y_3610_ = v___y_3690_;
v___y_3611_ = v___y_3691_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v___y_3693_;
v___y_3614_ = v___y_3694_;
v___y_3615_ = v___y_3695_;
goto v___jp_3593_;
}
else
{
lean_object* v_inheritedTraceOptions_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; 
v_inheritedTraceOptions_3707_ = lean_ctor_get(v___y_3694_, 13);
v___x_3708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3707_, v_options_3705_, v___x_3708_);
if (v___x_3709_ == 0)
{
lean_inc_ref(v_self_3696_);
lean_inc_ref(v_next_3697_);
lean_inc(v_size_3698_);
v___y_3594_ = v_size_3698_;
v___y_3595_ = v_next_3697_;
v___y_3596_ = v_root_3703_;
v___y_3597_ = v_fns_u2082_3685_;
v___y_3598_ = v_self_3696_;
v___y_3599_ = v_a_3702_;
v___y_3600_ = v___y_3682_;
v___y_3601_ = v___y_3681_;
v___y_3602_ = v___y_3683_;
v___y_3603_ = v_hasLambdas_3699_;
v___y_3604_ = v_heqProofs_3700_;
v___y_3605_ = v___y_3684_;
v___y_3606_ = v___y_3686_;
v___y_3607_ = v___y_3687_;
v___y_3608_ = v___y_3688_;
v___y_3609_ = v___y_3689_;
v___y_3610_ = v___y_3690_;
v___y_3611_ = v___y_3691_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v___y_3693_;
v___y_3614_ = v___y_3694_;
v___y_3615_ = v___y_3695_;
goto v___jp_3593_;
}
else
{
lean_object* v___x_3710_; 
v___x_3710_ = l_Lean_Meta_Grind_updateLastTag(v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v___x_3711_; 
lean_dec_ref(v___x_3710_);
lean_inc_ref(v_lhs_3420_);
v___x_3711_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3420_, v___y_3686_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref(v___x_3711_);
lean_inc_ref(v_root_3703_);
v___x_3713_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3703_, v___y_3686_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref(v___x_3713_);
v___x_3715_ = lean_st_ref_get(v___y_3686_);
lean_inc_ref(v_lhs_3420_);
v___x_3716_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3715_, v_lhs_3420_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___x_3715_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3718_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref(v___x_3716_);
v___x_3718_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3717_, v___y_3686_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref(v___x_3718_);
v___x_3720_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3721_, 0, v_a_3712_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
lean_ctor_set(v___x_3722_, 1, v_a_3714_);
v___x_3723_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
lean_ctor_set(v___x_3725_, 1, v_a_3719_);
v___x_3726_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3679_, v___x_3725_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_dec_ref(v___x_3726_);
lean_inc_ref(v_self_3696_);
lean_inc_ref(v_next_3697_);
lean_inc(v_size_3698_);
v___y_3594_ = v_size_3698_;
v___y_3595_ = v_next_3697_;
v___y_3596_ = v_root_3703_;
v___y_3597_ = v_fns_u2082_3685_;
v___y_3598_ = v_self_3696_;
v___y_3599_ = v_a_3702_;
v___y_3600_ = v___y_3682_;
v___y_3601_ = v___y_3681_;
v___y_3602_ = v___y_3683_;
v___y_3603_ = v_hasLambdas_3699_;
v___y_3604_ = v_heqProofs_3700_;
v___y_3605_ = v___y_3684_;
v___y_3606_ = v___y_3686_;
v___y_3607_ = v___y_3687_;
v___y_3608_ = v___y_3688_;
v___y_3609_ = v___y_3689_;
v___y_3610_ = v___y_3690_;
v___y_3611_ = v___y_3691_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v___y_3693_;
v___y_3614_ = v___y_3694_;
v___y_3615_ = v___y_3695_;
goto v___jp_3593_;
}
else
{
lean_dec_ref(v_root_3703_);
lean_dec(v_a_3702_);
lean_dec_ref(v_fns_u2082_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_lhs_3420_);
return v___x_3726_;
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec(v_a_3714_);
lean_dec(v_a_3712_);
lean_dec_ref(v_root_3703_);
lean_dec(v_a_3702_);
lean_dec_ref(v_fns_u2082_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_lhs_3420_);
v_a_3727_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3718_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3718_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec(v_a_3714_);
lean_dec(v_a_3712_);
lean_dec_ref(v_root_3703_);
lean_dec(v_a_3702_);
lean_dec_ref(v_fns_u2082_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_lhs_3420_);
v_a_3735_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3716_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3716_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec(v_a_3712_);
lean_dec_ref(v_root_3703_);
lean_dec(v_a_3702_);
lean_dec_ref(v_fns_u2082_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_lhs_3420_);
v_a_3743_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3713_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3713_);
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
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec_ref(v_root_3703_);
lean_dec(v_a_3702_);
lean_dec_ref(v_fns_u2082_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_lhs_3420_);
v_a_3751_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3711_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3711_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
else
{
lean_dec_ref(v_root_3703_);
lean_dec(v_a_3702_);
lean_dec_ref(v_fns_u2082_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_lhs_3420_);
return v___x_3710_;
}
}
}
}
else
{
lean_dec_ref(v_root_3703_);
lean_dec(v_a_3702_);
lean_dec_ref(v_fns_u2082_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_lhs_3420_);
return v___x_3704_;
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec_ref(v_fns_u2082_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhs_3420_);
v_a_3759_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3701_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3701_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
v___jp_3767_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3782_ = lean_array_get_size(v___y_3769_);
v___x_3783_ = lean_unsigned_to_nat(0u);
v___x_3784_ = lean_nat_dec_eq(v___x_3782_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_object* v_self_3785_; lean_object* v___x_3786_; 
v_self_3785_ = lean_ctor_get(v_lhsRoot_3424_, 0);
lean_inc_ref(v_self_3785_);
v___x_3786_ = l_Lean_Meta_Grind_getFnRoots(v_self_3785_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref(v___x_3786_);
v___y_3681_ = v___y_3769_;
v___y_3682_ = v___y_3768_;
v___y_3683_ = v_fns_u2081_3771_;
v___y_3684_ = v___y_3770_;
v_fns_u2082_3685_ = v_a_3787_;
v___y_3686_ = v___y_3772_;
v___y_3687_ = v___y_3773_;
v___y_3688_ = v___y_3774_;
v___y_3689_ = v___y_3775_;
v___y_3690_ = v___y_3776_;
v___y_3691_ = v___y_3777_;
v___y_3692_ = v___y_3778_;
v___y_3693_ = v___y_3779_;
v___y_3694_ = v___y_3780_;
v___y_3695_ = v___y_3781_;
goto v___jp_3680_;
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref(v_fns_u2081_3771_);
lean_dec_ref(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhs_3420_);
v_a_3788_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3786_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3786_);
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
lean_object* v___x_3796_; 
v___x_3796_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3681_ = v___y_3769_;
v___y_3682_ = v___y_3768_;
v___y_3683_ = v_fns_u2081_3771_;
v___y_3684_ = v___y_3770_;
v_fns_u2082_3685_ = v___x_3796_;
v___y_3686_ = v___y_3772_;
v___y_3687_ = v___y_3773_;
v___y_3688_ = v___y_3774_;
v___y_3689_ = v___y_3775_;
v___y_3690_ = v___y_3776_;
v___y_3691_ = v___y_3777_;
v___y_3692_ = v___y_3778_;
v___y_3693_ = v___y_3779_;
v___y_3694_ = v___y_3780_;
v___y_3695_ = v___y_3781_;
goto v___jp_3680_;
}
}
v___jp_3797_:
{
lean_object* v___x_3808_; 
lean_inc_ref(v_lhs_3420_);
v___x_3808_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3420_, v___y_3798_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3876_; 
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3876_ == 0)
{
lean_object* v_unused_3877_; 
v_unused_3877_ = lean_ctor_get(v___x_3808_, 0);
lean_dec(v_unused_3877_);
v___x_3810_ = v___x_3808_;
v_isShared_3811_ = v_isSharedCheck_3876_;
goto v_resetjp_3809_;
}
else
{
lean_dec(v___x_3808_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3876_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v_self_3812_; lean_object* v_next_3813_; lean_object* v_root_3814_; lean_object* v_congr_3815_; lean_object* v_size_3816_; uint8_t v_interpreted_3817_; uint8_t v_ctor_3818_; uint8_t v_hasLambdas_3819_; uint8_t v_heqProofs_3820_; lean_object* v_idx_3821_; lean_object* v_generation_3822_; lean_object* v_mt_3823_; lean_object* v_sTerms_3824_; uint8_t v_funCC_3825_; lean_object* v_ematchDiagSource_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3873_; 
v_self_3812_ = lean_ctor_get(v_lhsNode_3422_, 0);
v_next_3813_ = lean_ctor_get(v_lhsNode_3422_, 1);
v_root_3814_ = lean_ctor_get(v_lhsNode_3422_, 2);
v_congr_3815_ = lean_ctor_get(v_lhsNode_3422_, 3);
v_size_3816_ = lean_ctor_get(v_lhsNode_3422_, 6);
v_interpreted_3817_ = lean_ctor_get_uint8(v_lhsNode_3422_, sizeof(void*)*12 + 1);
v_ctor_3818_ = lean_ctor_get_uint8(v_lhsNode_3422_, sizeof(void*)*12 + 2);
v_hasLambdas_3819_ = lean_ctor_get_uint8(v_lhsNode_3422_, sizeof(void*)*12 + 3);
v_heqProofs_3820_ = lean_ctor_get_uint8(v_lhsNode_3422_, sizeof(void*)*12 + 4);
v_idx_3821_ = lean_ctor_get(v_lhsNode_3422_, 7);
v_generation_3822_ = lean_ctor_get(v_lhsNode_3422_, 8);
v_mt_3823_ = lean_ctor_get(v_lhsNode_3422_, 9);
v_sTerms_3824_ = lean_ctor_get(v_lhsNode_3422_, 10);
v_funCC_3825_ = lean_ctor_get_uint8(v_lhsNode_3422_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3826_ = lean_ctor_get(v_lhsNode_3422_, 11);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_lhsNode_3422_);
if (v_isSharedCheck_3873_ == 0)
{
lean_object* v_unused_3874_; lean_object* v_unused_3875_; 
v_unused_3874_ = lean_ctor_get(v_lhsNode_3422_, 5);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_lhsNode_3422_, 4);
lean_dec(v_unused_3875_);
v___x_3828_ = v_lhsNode_3422_;
v_isShared_3829_ = v_isSharedCheck_3873_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_ematchDiagSource_3826_);
lean_inc(v_sTerms_3824_);
lean_inc(v_mt_3823_);
lean_inc(v_generation_3822_);
lean_inc(v_idx_3821_);
lean_inc(v_size_3816_);
lean_inc(v_congr_3815_);
lean_inc(v_root_3814_);
lean_inc(v_next_3813_);
lean_inc(v_self_3812_);
lean_dec(v_lhsNode_3422_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3873_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set_tag(v___x_3810_, 1);
lean_ctor_set(v___x_3810_, 0, v_rhs_3421_);
v___x_3831_ = v___x_3810_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_rhs_3421_);
v___x_3831_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3832_, 0, v_proof_3418_);
lean_inc_ref(v_root_3814_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 5, v___x_3832_);
lean_ctor_set(v___x_3828_, 4, v___x_3831_);
v___x_3834_ = v___x_3828_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_self_3812_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_next_3813_);
lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_root_3814_);
lean_ctor_set(v_reuseFailAlloc_3871_, 3, v_congr_3815_);
lean_ctor_set(v_reuseFailAlloc_3871_, 4, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3871_, 5, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3871_, 6, v_size_3816_);
lean_ctor_set(v_reuseFailAlloc_3871_, 7, v_idx_3821_);
lean_ctor_set(v_reuseFailAlloc_3871_, 8, v_generation_3822_);
lean_ctor_set(v_reuseFailAlloc_3871_, 9, v_mt_3823_);
lean_ctor_set(v_reuseFailAlloc_3871_, 10, v_sTerms_3824_);
lean_ctor_set(v_reuseFailAlloc_3871_, 11, v_ematchDiagSource_3826_);
lean_ctor_set_uint8(v_reuseFailAlloc_3871_, sizeof(void*)*12 + 1, v_interpreted_3817_);
lean_ctor_set_uint8(v_reuseFailAlloc_3871_, sizeof(void*)*12 + 2, v_ctor_3818_);
lean_ctor_set_uint8(v_reuseFailAlloc_3871_, sizeof(void*)*12 + 3, v_hasLambdas_3819_);
lean_ctor_set_uint8(v_reuseFailAlloc_3871_, sizeof(void*)*12 + 4, v_heqProofs_3820_);
lean_ctor_set_uint8(v_reuseFailAlloc_3871_, sizeof(void*)*12 + 5, v_funCC_3825_);
v___x_3834_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3835_; 
lean_ctor_set_uint8(v___x_3834_, sizeof(void*)*12, v_flipped_3426_);
lean_inc_ref(v_lhs_3420_);
v___x_3835_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3420_, v___x_3834_, v___y_3798_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v___x_3836_; 
lean_dec_ref(v___x_3835_);
v___x_3836_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3424_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3838_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref(v___x_3836_);
v___x_3838_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3425_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v___x_3838_);
v___x_3840_ = lean_array_get_size(v_a_3837_);
v___x_3841_ = lean_unsigned_to_nat(0u);
v___x_3842_ = lean_nat_dec_eq(v___x_3840_, v___x_3841_);
if (v___x_3842_ == 0)
{
lean_object* v_self_3843_; lean_object* v___x_3844_; 
v_self_3843_ = lean_ctor_get(v_rhsRoot_3425_, 0);
lean_inc_ref(v_self_3843_);
v___x_3844_ = l_Lean_Meta_Grind_getFnRoots(v_self_3843_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref(v___x_3844_);
v___y_3768_ = v_a_3837_;
v___y_3769_ = v_a_3839_;
v___y_3770_ = v_root_3814_;
v_fns_u2081_3771_ = v_a_3845_;
v___y_3772_ = v___y_3798_;
v___y_3773_ = v___y_3799_;
v___y_3774_ = v___y_3800_;
v___y_3775_ = v___y_3801_;
v___y_3776_ = v___y_3802_;
v___y_3777_ = v___y_3803_;
v___y_3778_ = v___y_3804_;
v___y_3779_ = v___y_3805_;
v___y_3780_ = v___y_3806_;
v___y_3781_ = v___y_3807_;
goto v___jp_3767_;
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_dec(v_a_3839_);
lean_dec(v_a_3837_);
lean_dec_ref(v_root_3814_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhs_3420_);
v_a_3846_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3844_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3844_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
else
{
lean_object* v___x_3854_; 
v___x_3854_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3768_ = v_a_3837_;
v___y_3769_ = v_a_3839_;
v___y_3770_ = v_root_3814_;
v_fns_u2081_3771_ = v___x_3854_;
v___y_3772_ = v___y_3798_;
v___y_3773_ = v___y_3799_;
v___y_3774_ = v___y_3800_;
v___y_3775_ = v___y_3801_;
v___y_3776_ = v___y_3802_;
v___y_3777_ = v___y_3803_;
v___y_3778_ = v___y_3804_;
v___y_3779_ = v___y_3805_;
v___y_3780_ = v___y_3806_;
v___y_3781_ = v___y_3807_;
goto v___jp_3767_;
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v_a_3837_);
lean_dec_ref(v_root_3814_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhs_3420_);
v_a_3855_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3838_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3838_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec_ref(v_root_3814_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhs_3420_);
v_a_3863_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3836_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3836_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
else
{
lean_dec_ref(v_root_3814_);
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhs_3420_);
return v___x_3835_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3425_);
lean_dec_ref(v_lhsRoot_3424_);
lean_dec_ref(v_rhsNode_3423_);
lean_dec_ref(v_lhsNode_3422_);
lean_dec_ref(v_rhs_3421_);
lean_dec_ref(v_lhs_3420_);
lean_dec_ref(v_proof_3418_);
return v___x_3808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3907_ = _args[0];
lean_object* v_isHEq_3908_ = _args[1];
lean_object* v_lhs_3909_ = _args[2];
lean_object* v_rhs_3910_ = _args[3];
lean_object* v_lhsNode_3911_ = _args[4];
lean_object* v_rhsNode_3912_ = _args[5];
lean_object* v_lhsRoot_3913_ = _args[6];
lean_object* v_rhsRoot_3914_ = _args[7];
lean_object* v_flipped_3915_ = _args[8];
lean_object* v_a_3916_ = _args[9];
lean_object* v_a_3917_ = _args[10];
lean_object* v_a_3918_ = _args[11];
lean_object* v_a_3919_ = _args[12];
lean_object* v_a_3920_ = _args[13];
lean_object* v_a_3921_ = _args[14];
lean_object* v_a_3922_ = _args[15];
lean_object* v_a_3923_ = _args[16];
lean_object* v_a_3924_ = _args[17];
lean_object* v_a_3925_ = _args[18];
lean_object* v_a_3926_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3927_; uint8_t v_flipped_boxed_3928_; lean_object* v_res_3929_; 
v_isHEq_boxed_3927_ = lean_unbox(v_isHEq_3908_);
v_flipped_boxed_3928_ = lean_unbox(v_flipped_3915_);
v_res_3929_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3907_, v_isHEq_boxed_3927_, v_lhs_3909_, v_rhs_3910_, v_lhsNode_3911_, v_rhsNode_3912_, v_lhsRoot_3913_, v_rhsRoot_3914_, v_flipped_boxed_3928_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
lean_dec_ref(v_a_3922_);
lean_dec(v_a_3921_);
lean_dec_ref(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec_ref(v_a_3918_);
lean_dec(v_a_3917_);
lean_dec(v_a_3916_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3930_, lean_object* v_as_x27_3931_, lean_object* v_b_3932_, lean_object* v_a_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3931_, v_b_3932_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3946_, lean_object* v_as_x27_3947_, lean_object* v_b_3948_, lean_object* v_a_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3946_, v_as_x27_3947_, v_b_3948_, v_a_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec(v_as_x27_3947_);
lean_dec(v_as_3946_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3962_, lean_object* v_as_x27_3963_, lean_object* v_b_3964_, lean_object* v_a_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v___x_3977_; 
v___x_3977_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3963_, v_b_3964_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3978_, lean_object* v_as_x27_3979_, lean_object* v_b_3980_, lean_object* v_a_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3978_, v_as_x27_3979_, v_b_3980_, v_a_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec(v_as_x27_3979_);
lean_dec(v_as_3978_);
return v_res_3993_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_3996_ = l_Lean_stringToMessageData(v___x_3995_);
return v___x_3996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4002_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4003_ = l_Lean_Name_append(v___x_4002_, v___x_4001_);
return v___x_4003_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4006_ = l_Lean_stringToMessageData(v___x_4005_);
return v___x_4006_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4009_ = l_Lean_stringToMessageData(v___x_4008_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4010_, lean_object* v_rhs_4011_, lean_object* v_proof_4012_, uint8_t v_isHEq_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4028_ = lean_st_ref_get(v_a_4014_);
lean_inc_ref(v_lhs_4010_);
v___x_4029_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4028_, v_lhs_4010_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
lean_dec(v___x_4028_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref(v___x_4029_);
v___x_4031_ = lean_st_ref_get(v_a_4014_);
lean_inc_ref(v_rhs_4011_);
v___x_4032_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4031_, v_rhs_4011_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
lean_dec(v___x_4031_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v_root_4034_; lean_object* v_root_4035_; uint8_t v___x_4036_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref(v___x_4032_);
v_root_4034_ = lean_ctor_get(v_a_4030_, 2);
v_root_4035_ = lean_ctor_get(v_a_4033_, 2);
v___x_4036_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_4034_, v_root_4035_);
if (v___x_4036_ == 0)
{
lean_object* v_options_4037_; lean_object* v_inheritedTraceOptions_4038_; uint8_t v_hasTrace_4039_; uint8_t v___x_4040_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4077_; uint8_t v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; uint8_t v___y_4116_; lean_object* v___y_4117_; uint8_t v___y_4118_; lean_object* v___y_4123_; uint8_t v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; uint8_t v___y_4150_; lean_object* v___y_4151_; uint8_t v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; uint8_t v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; uint8_t v___y_4179_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; uint8_t v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; uint8_t v___y_4195_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; uint8_t v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; uint8_t v___y_4211_; uint8_t v___y_4212_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v_size_4217_; uint8_t v_interpreted_4218_; uint8_t v_ctor_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; uint8_t v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v_size_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; uint8_t v___y_4231_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; uint8_t v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; uint8_t v___y_4247_; uint8_t v___y_4248_; lean_object* v___y_4259_; uint8_t v_interpreted_4260_; lean_object* v___y_4261_; uint8_t v_valueInconsistency_4262_; uint8_t v_trueEqFalse_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4276_; lean_object* v___y_4277_; uint8_t v_valueInconsistency_4278_; uint8_t v_trueEqFalse_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4306_; lean_object* v___y_4307_; uint8_t v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; uint8_t v___y_4346_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; 
v_options_4037_ = lean_ctor_get(v_a_4022_, 2);
v_inheritedTraceOptions_4038_ = lean_ctor_get(v_a_4022_, 13);
v_hasTrace_4039_ = lean_ctor_get_uint8(v_options_4037_, sizeof(void*)*1);
v___x_4040_ = 1;
if (v_hasTrace_4039_ == 0)
{
v___y_4353_ = v_a_4014_;
v___y_4354_ = v_a_4015_;
v___y_4355_ = v_a_4016_;
v___y_4356_ = v_a_4017_;
v___y_4357_ = v_a_4018_;
v___y_4358_ = v_a_4019_;
v___y_4359_ = v_a_4020_;
v___y_4360_ = v_a_4021_;
v___y_4361_ = v_a_4022_;
v___y_4362_ = v_a_4023_;
goto v___jp_4352_;
}
else
{
lean_object* v___x_4388_; lean_object* v___y_4390_; lean_object* v___x_4402_; uint8_t v___x_4403_; 
v___x_4388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4403_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4038_, v_options_4037_, v___x_4402_);
if (v___x_4403_ == 0)
{
v___y_4353_ = v_a_4014_;
v___y_4354_ = v_a_4015_;
v___y_4355_ = v_a_4016_;
v___y_4356_ = v_a_4017_;
v___y_4357_ = v_a_4018_;
v___y_4358_ = v_a_4019_;
v___y_4359_ = v_a_4020_;
v___y_4360_ = v_a_4021_;
v___y_4361_ = v_a_4022_;
v___y_4362_ = v_a_4023_;
goto v___jp_4352_;
}
else
{
lean_object* v___x_4404_; 
v___x_4404_ = l_Lean_Meta_Grind_updateLastTag(v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_dec_ref(v___x_4404_);
if (v_isHEq_4013_ == 0)
{
lean_object* v___x_4405_; 
lean_inc_ref(v_rhs_4011_);
lean_inc_ref(v_lhs_4010_);
v___x_4405_ = l_Lean_Meta_mkEq(v_lhs_4010_, v_rhs_4011_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
v___y_4390_ = v___x_4405_;
goto v___jp_4389_;
}
else
{
lean_object* v___x_4406_; 
lean_inc_ref(v_rhs_4011_);
lean_inc_ref(v_lhs_4010_);
v___x_4406_ = l_Lean_Meta_mkHEq(v_lhs_4010_, v_rhs_4011_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
v___y_4390_ = v___x_4406_;
goto v___jp_4389_;
}
}
else
{
lean_dec(v_a_4033_);
lean_dec(v_a_4030_);
lean_dec_ref(v_proof_4012_);
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
return v___x_4404_;
}
}
v___jp_4389_:
{
if (lean_obj_tag(v___y_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v_a_4391_ = lean_ctor_get(v___y_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref(v___y_4390_);
v___x_4392_ = l_Lean_MessageData_ofExpr(v_a_4391_);
v___x_4393_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4388_, v___x_4392_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_dec_ref(v___x_4393_);
v___y_4353_ = v_a_4014_;
v___y_4354_ = v_a_4015_;
v___y_4355_ = v_a_4016_;
v___y_4356_ = v_a_4017_;
v___y_4357_ = v_a_4018_;
v___y_4358_ = v_a_4019_;
v___y_4359_ = v_a_4020_;
v___y_4360_ = v_a_4021_;
v___y_4361_ = v_a_4022_;
v___y_4362_ = v_a_4023_;
goto v___jp_4352_;
}
else
{
lean_dec(v_a_4033_);
lean_dec(v_a_4030_);
lean_dec_ref(v_proof_4012_);
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
return v___x_4393_;
}
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
lean_dec(v_a_4033_);
lean_dec(v_a_4030_);
lean_dec_ref(v_proof_4012_);
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
v_a_4394_ = lean_ctor_get(v___y_4390_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___y_4390_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___y_4390_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___y_4390_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
}
v___jp_4041_:
{
lean_object* v_options_4052_; uint8_t v_hasTrace_4053_; 
v_options_4052_ = lean_ctor_get(v___y_4050_, 2);
v_hasTrace_4053_ = lean_ctor_get_uint8(v_options_4052_, sizeof(void*)*1);
if (v_hasTrace_4053_ == 0)
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Lean_Meta_Grind_checkInvariants(v___x_4036_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
return v___x_4054_;
}
else
{
lean_object* v_inheritedTraceOptions_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; 
v_inheritedTraceOptions_4055_ = lean_ctor_get(v___y_4050_, 13);
v___x_4056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4057_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4058_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4055_, v_options_4052_, v___x_4057_);
if (v___x_4058_ == 0)
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Lean_Meta_Grind_checkInvariants(v___x_4036_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
return v___x_4059_;
}
else
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Lean_Meta_Grind_updateLastTag(v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
lean_dec_ref(v___x_4060_);
v___x_4061_ = lean_st_ref_get(v___y_4042_);
v___x_4062_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4061_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___x_4061_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref(v___x_4062_);
v___x_4064_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
lean_ctor_set(v___x_4065_, 1, v_a_4063_);
v___x_4066_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4056_, v___x_4065_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v___x_4067_; 
lean_dec_ref(v___x_4066_);
v___x_4067_ = l_Lean_Meta_Grind_checkInvariants(v___x_4036_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
return v___x_4067_;
}
else
{
return v___x_4066_;
}
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
v_a_4068_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4062_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4062_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
else
{
return v___x_4060_;
}
}
}
}
v___jp_4076_:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4080_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; uint8_t v___x_4092_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref(v___x_4090_);
v___x_4092_ = lean_unbox(v_a_4091_);
lean_dec(v_a_4091_);
if (v___x_4092_ == 0)
{
if (v___y_4078_ == 0)
{
lean_dec_ref(v___y_4079_);
lean_dec_ref(v___y_4077_);
v___y_4042_ = v___y_4080_;
v___y_4043_ = v___y_4081_;
v___y_4044_ = v___y_4082_;
v___y_4045_ = v___y_4083_;
v___y_4046_ = v___y_4084_;
v___y_4047_ = v___y_4085_;
v___y_4048_ = v___y_4086_;
v___y_4049_ = v___y_4087_;
v___y_4050_ = v___y_4088_;
v___y_4051_ = v___y_4089_;
goto v___jp_4041_;
}
else
{
lean_object* v_self_4093_; lean_object* v_self_4094_; lean_object* v___x_4095_; 
v_self_4093_ = lean_ctor_get(v___y_4077_, 0);
lean_inc_ref(v_self_4093_);
lean_dec_ref(v___y_4077_);
v_self_4094_ = lean_ctor_get(v___y_4079_, 0);
lean_inc_ref(v_self_4094_);
lean_dec_ref(v___y_4079_);
v___x_4095_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4093_, v_self_4094_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_dec_ref(v___x_4095_);
v___y_4042_ = v___y_4080_;
v___y_4043_ = v___y_4081_;
v___y_4044_ = v___y_4082_;
v___y_4045_ = v___y_4083_;
v___y_4046_ = v___y_4084_;
v___y_4047_ = v___y_4085_;
v___y_4048_ = v___y_4086_;
v___y_4049_ = v___y_4087_;
v___y_4050_ = v___y_4088_;
v___y_4051_ = v___y_4089_;
goto v___jp_4041_;
}
else
{
return v___x_4095_;
}
}
}
else
{
lean_dec_ref(v___y_4079_);
lean_dec_ref(v___y_4077_);
v___y_4042_ = v___y_4080_;
v___y_4043_ = v___y_4081_;
v___y_4044_ = v___y_4082_;
v___y_4045_ = v___y_4083_;
v___y_4046_ = v___y_4084_;
v___y_4047_ = v___y_4085_;
v___y_4048_ = v___y_4086_;
v___y_4049_ = v___y_4087_;
v___y_4050_ = v___y_4088_;
v___y_4051_ = v___y_4089_;
goto v___jp_4041_;
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec_ref(v___y_4079_);
lean_dec_ref(v___y_4077_);
v_a_4096_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4090_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4090_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
v___jp_4104_:
{
if (v___y_4118_ == 0)
{
v___y_4077_ = v___y_4114_;
v___y_4078_ = v___y_4116_;
v___y_4079_ = v___y_4111_;
v___y_4080_ = v___y_4108_;
v___y_4081_ = v___y_4113_;
v___y_4082_ = v___y_4105_;
v___y_4083_ = v___y_4109_;
v___y_4084_ = v___y_4112_;
v___y_4085_ = v___y_4107_;
v___y_4086_ = v___y_4117_;
v___y_4087_ = v___y_4110_;
v___y_4088_ = v___y_4106_;
v___y_4089_ = v___y_4115_;
goto v___jp_4076_;
}
else
{
lean_object* v_self_4119_; lean_object* v_self_4120_; lean_object* v___x_4121_; 
v_self_4119_ = lean_ctor_get(v___y_4114_, 0);
v_self_4120_ = lean_ctor_get(v___y_4111_, 0);
lean_inc_ref(v_self_4120_);
lean_inc_ref(v_self_4119_);
v___x_4121_ = l_Lean_Meta_Grind_propagateCtor(v_self_4119_, v_self_4120_, v___y_4108_, v___y_4113_, v___y_4105_, v___y_4109_, v___y_4112_, v___y_4107_, v___y_4117_, v___y_4110_, v___y_4106_, v___y_4115_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_dec_ref(v___x_4121_);
v___y_4077_ = v___y_4114_;
v___y_4078_ = v___y_4116_;
v___y_4079_ = v___y_4111_;
v___y_4080_ = v___y_4108_;
v___y_4081_ = v___y_4113_;
v___y_4082_ = v___y_4105_;
v___y_4083_ = v___y_4109_;
v___y_4084_ = v___y_4112_;
v___y_4085_ = v___y_4107_;
v___y_4086_ = v___y_4117_;
v___y_4087_ = v___y_4110_;
v___y_4088_ = v___y_4106_;
v___y_4089_ = v___y_4115_;
goto v___jp_4076_;
}
else
{
lean_dec_ref(v___y_4114_);
lean_dec_ref(v___y_4111_);
return v___x_4121_;
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
lean_dec_ref(v___x_4136_);
v___x_4138_ = lean_unbox(v_a_4137_);
lean_dec(v_a_4137_);
if (v___x_4138_ == 0)
{
uint8_t v_ctor_4139_; 
v_ctor_4139_ = lean_ctor_get_uint8(v___y_4123_, sizeof(void*)*12 + 2);
if (v_ctor_4139_ == 0)
{
v___y_4105_ = v___y_4128_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4131_;
v___y_4108_ = v___y_4126_;
v___y_4109_ = v___y_4129_;
v___y_4110_ = v___y_4133_;
v___y_4111_ = v___y_4125_;
v___y_4112_ = v___y_4130_;
v___y_4113_ = v___y_4127_;
v___y_4114_ = v___y_4123_;
v___y_4115_ = v___y_4135_;
v___y_4116_ = v___y_4124_;
v___y_4117_ = v___y_4132_;
v___y_4118_ = v___x_4036_;
goto v___jp_4104_;
}
else
{
uint8_t v_ctor_4140_; 
v_ctor_4140_ = lean_ctor_get_uint8(v___y_4125_, sizeof(void*)*12 + 2);
v___y_4105_ = v___y_4128_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4131_;
v___y_4108_ = v___y_4126_;
v___y_4109_ = v___y_4129_;
v___y_4110_ = v___y_4133_;
v___y_4111_ = v___y_4125_;
v___y_4112_ = v___y_4130_;
v___y_4113_ = v___y_4127_;
v___y_4114_ = v___y_4123_;
v___y_4115_ = v___y_4135_;
v___y_4116_ = v___y_4124_;
v___y_4117_ = v___y_4132_;
v___y_4118_ = v_ctor_4140_;
goto v___jp_4104_;
}
}
else
{
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
v___y_4089_ = v___y_4135_;
goto v___jp_4076_;
}
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v___y_4125_);
lean_dec_ref(v___y_4123_);
v_a_4141_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4136_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4136_);
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
if (v___y_4150_ == 0)
{
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
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
v___y_4135_ = v___y_4163_;
goto v___jp_4122_;
}
else
{
lean_object* v___x_4164_; 
v___x_4164_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_dec_ref(v___x_4164_);
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
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
v___y_4135_ = v___y_4163_;
goto v___jp_4122_;
}
else
{
lean_dec_ref(v___y_4153_);
lean_dec_ref(v___y_4151_);
return v___x_4164_;
}
}
}
v___jp_4165_:
{
lean_object* v___x_4180_; 
lean_inc_ref(v___y_4176_);
lean_inc_ref(v___y_4168_);
v___x_4180_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4012_, v_isHEq_4013_, v_rhs_4011_, v_lhs_4010_, v_a_4033_, v_a_4030_, v___y_4168_, v___y_4176_, v___x_4040_, v___y_4171_, v___y_4172_, v___y_4167_, v___y_4169_, v___y_4170_, v___y_4177_, v___y_4175_, v___y_4178_, v___y_4166_, v___y_4174_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_dec_ref(v___x_4180_);
v___y_4150_ = v___y_4173_;
v___y_4151_ = v___y_4176_;
v___y_4152_ = v___y_4179_;
v___y_4153_ = v___y_4168_;
v___y_4154_ = v___y_4171_;
v___y_4155_ = v___y_4172_;
v___y_4156_ = v___y_4167_;
v___y_4157_ = v___y_4169_;
v___y_4158_ = v___y_4170_;
v___y_4159_ = v___y_4177_;
v___y_4160_ = v___y_4175_;
v___y_4161_ = v___y_4178_;
v___y_4162_ = v___y_4166_;
v___y_4163_ = v___y_4174_;
goto v___jp_4149_;
}
else
{
lean_dec_ref(v___y_4176_);
lean_dec_ref(v___y_4168_);
return v___x_4180_;
}
}
v___jp_4181_:
{
lean_object* v___x_4196_; 
lean_inc_ref(v___y_4184_);
lean_inc_ref(v___y_4192_);
v___x_4196_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4012_, v_isHEq_4013_, v_lhs_4010_, v_rhs_4011_, v_a_4030_, v_a_4033_, v___y_4192_, v___y_4184_, v___x_4036_, v___y_4187_, v___y_4188_, v___y_4183_, v___y_4185_, v___y_4186_, v___y_4193_, v___y_4191_, v___y_4194_, v___y_4182_, v___y_4190_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_dec_ref(v___x_4196_);
v___y_4150_ = v___y_4189_;
v___y_4151_ = v___y_4192_;
v___y_4152_ = v___y_4195_;
v___y_4153_ = v___y_4184_;
v___y_4154_ = v___y_4187_;
v___y_4155_ = v___y_4188_;
v___y_4156_ = v___y_4183_;
v___y_4157_ = v___y_4185_;
v___y_4158_ = v___y_4186_;
v___y_4159_ = v___y_4193_;
v___y_4160_ = v___y_4191_;
v___y_4161_ = v___y_4194_;
v___y_4162_ = v___y_4182_;
v___y_4163_ = v___y_4190_;
goto v___jp_4149_;
}
else
{
lean_dec_ref(v___y_4192_);
lean_dec_ref(v___y_4184_);
return v___x_4196_;
}
}
v___jp_4197_:
{
if (v___y_4212_ == 0)
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
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4208_;
v___y_4193_ = v___y_4209_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___y_4211_;
goto v___jp_4181_;
}
else
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
v___y_4175_ = v___y_4207_;
v___y_4176_ = v___y_4208_;
v___y_4177_ = v___y_4209_;
v___y_4178_ = v___y_4210_;
v___y_4179_ = v___y_4211_;
goto v___jp_4165_;
}
}
v___jp_4213_:
{
uint8_t v___x_4232_; 
v___x_4232_ = lean_nat_dec_lt(v_size_4217_, v_size_4228_);
lean_dec(v_size_4228_);
lean_dec(v_size_4217_);
if (v___x_4232_ == 0)
{
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4220_;
v___y_4202_ = v___y_4221_;
v___y_4203_ = v___y_4222_;
v___y_4204_ = v___y_4223_;
v___y_4205_ = v___y_4224_;
v___y_4206_ = v___y_4225_;
v___y_4207_ = v___y_4226_;
v___y_4208_ = v___y_4227_;
v___y_4209_ = v___y_4229_;
v___y_4210_ = v___y_4230_;
v___y_4211_ = v___y_4231_;
v___y_4212_ = v___x_4036_;
goto v___jp_4197_;
}
else
{
if (v_interpreted_4218_ == 0)
{
if (v___x_4232_ == 0)
{
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4220_;
v___y_4202_ = v___y_4221_;
v___y_4203_ = v___y_4222_;
v___y_4204_ = v___y_4223_;
v___y_4205_ = v___y_4224_;
v___y_4206_ = v___y_4225_;
v___y_4207_ = v___y_4226_;
v___y_4208_ = v___y_4227_;
v___y_4209_ = v___y_4229_;
v___y_4210_ = v___y_4230_;
v___y_4211_ = v___y_4231_;
v___y_4212_ = v___x_4036_;
goto v___jp_4197_;
}
else
{
if (v_ctor_4219_ == 0)
{
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4220_;
v___y_4202_ = v___y_4221_;
v___y_4203_ = v___y_4222_;
v___y_4204_ = v___y_4223_;
v___y_4205_ = v___y_4224_;
v___y_4206_ = v___y_4225_;
v___y_4207_ = v___y_4226_;
v___y_4208_ = v___y_4227_;
v___y_4209_ = v___y_4229_;
v___y_4210_ = v___y_4230_;
v___y_4211_ = v___y_4231_;
v___y_4212_ = v___x_4232_;
goto v___jp_4197_;
}
else
{
v___y_4182_ = v___y_4214_;
v___y_4183_ = v___y_4215_;
v___y_4184_ = v___y_4216_;
v___y_4185_ = v___y_4220_;
v___y_4186_ = v___y_4221_;
v___y_4187_ = v___y_4222_;
v___y_4188_ = v___y_4223_;
v___y_4189_ = v___y_4224_;
v___y_4190_ = v___y_4225_;
v___y_4191_ = v___y_4226_;
v___y_4192_ = v___y_4227_;
v___y_4193_ = v___y_4229_;
v___y_4194_ = v___y_4230_;
v___y_4195_ = v___y_4231_;
goto v___jp_4181_;
}
}
}
else
{
v___y_4198_ = v___y_4214_;
v___y_4199_ = v___y_4215_;
v___y_4200_ = v___y_4216_;
v___y_4201_ = v___y_4220_;
v___y_4202_ = v___y_4221_;
v___y_4203_ = v___y_4222_;
v___y_4204_ = v___y_4223_;
v___y_4205_ = v___y_4224_;
v___y_4206_ = v___y_4225_;
v___y_4207_ = v___y_4226_;
v___y_4208_ = v___y_4227_;
v___y_4209_ = v___y_4229_;
v___y_4210_ = v___y_4230_;
v___y_4211_ = v___y_4231_;
v___y_4212_ = v___x_4036_;
goto v___jp_4197_;
}
}
}
v___jp_4233_:
{
if (v___y_4248_ == 0)
{
uint8_t v_ctor_4249_; 
v_ctor_4249_ = lean_ctor_get_uint8(v___y_4244_, sizeof(void*)*12 + 2);
if (v_ctor_4249_ == 0)
{
if (v___x_4036_ == 0)
{
lean_object* v_size_4250_; lean_object* v_size_4251_; uint8_t v_interpreted_4252_; uint8_t v_ctor_4253_; 
v_size_4250_ = lean_ctor_get(v___y_4244_, 6);
lean_inc(v_size_4250_);
v_size_4251_ = lean_ctor_get(v___y_4236_, 6);
lean_inc(v_size_4251_);
v_interpreted_4252_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 1);
v_ctor_4253_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 2);
v___y_4214_ = v___y_4234_;
v___y_4215_ = v___y_4235_;
v___y_4216_ = v___y_4236_;
v_size_4217_ = v_size_4251_;
v_interpreted_4218_ = v_interpreted_4252_;
v_ctor_4219_ = v_ctor_4253_;
v___y_4220_ = v___y_4237_;
v___y_4221_ = v___y_4238_;
v___y_4222_ = v___y_4239_;
v___y_4223_ = v___y_4240_;
v___y_4224_ = v___y_4241_;
v___y_4225_ = v___y_4242_;
v___y_4226_ = v___y_4243_;
v___y_4227_ = v___y_4244_;
v_size_4228_ = v_size_4250_;
v___y_4229_ = v___y_4245_;
v___y_4230_ = v___y_4246_;
v___y_4231_ = v___y_4247_;
goto v___jp_4213_;
}
else
{
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
v___y_4176_ = v___y_4244_;
v___y_4177_ = v___y_4245_;
v___y_4178_ = v___y_4246_;
v___y_4179_ = v___y_4247_;
goto v___jp_4165_;
}
}
else
{
uint8_t v_ctor_4254_; 
v_ctor_4254_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 2);
if (v_ctor_4254_ == 0)
{
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
v___y_4176_ = v___y_4244_;
v___y_4177_ = v___y_4245_;
v___y_4178_ = v___y_4246_;
v___y_4179_ = v___y_4247_;
goto v___jp_4165_;
}
else
{
lean_object* v_size_4255_; lean_object* v_size_4256_; uint8_t v_interpreted_4257_; 
v_size_4255_ = lean_ctor_get(v___y_4244_, 6);
lean_inc(v_size_4255_);
v_size_4256_ = lean_ctor_get(v___y_4236_, 6);
lean_inc(v_size_4256_);
v_interpreted_4257_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 1);
v___y_4214_ = v___y_4234_;
v___y_4215_ = v___y_4235_;
v___y_4216_ = v___y_4236_;
v_size_4217_ = v_size_4256_;
v_interpreted_4218_ = v_interpreted_4257_;
v_ctor_4219_ = v_ctor_4254_;
v___y_4220_ = v___y_4237_;
v___y_4221_ = v___y_4238_;
v___y_4222_ = v___y_4239_;
v___y_4223_ = v___y_4240_;
v___y_4224_ = v___y_4241_;
v___y_4225_ = v___y_4242_;
v___y_4226_ = v___y_4243_;
v___y_4227_ = v___y_4244_;
v_size_4228_ = v_size_4255_;
v___y_4229_ = v___y_4245_;
v___y_4230_ = v___y_4246_;
v___y_4231_ = v___y_4247_;
goto v___jp_4213_;
}
}
}
else
{
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
v___y_4176_ = v___y_4244_;
v___y_4177_ = v___y_4245_;
v___y_4178_ = v___y_4246_;
v___y_4179_ = v___y_4247_;
goto v___jp_4165_;
}
}
v___jp_4258_:
{
if (v_interpreted_4260_ == 0)
{
v___y_4234_ = v___y_4272_;
v___y_4235_ = v___y_4266_;
v___y_4236_ = v___y_4261_;
v___y_4237_ = v___y_4267_;
v___y_4238_ = v___y_4268_;
v___y_4239_ = v___y_4264_;
v___y_4240_ = v___y_4265_;
v___y_4241_ = v_trueEqFalse_4263_;
v___y_4242_ = v___y_4273_;
v___y_4243_ = v___y_4270_;
v___y_4244_ = v___y_4259_;
v___y_4245_ = v___y_4269_;
v___y_4246_ = v___y_4271_;
v___y_4247_ = v_valueInconsistency_4262_;
v___y_4248_ = v___x_4036_;
goto v___jp_4233_;
}
else
{
uint8_t v_interpreted_4274_; 
v_interpreted_4274_ = lean_ctor_get_uint8(v___y_4261_, sizeof(void*)*12 + 1);
if (v_interpreted_4274_ == 0)
{
v___y_4166_ = v___y_4272_;
v___y_4167_ = v___y_4266_;
v___y_4168_ = v___y_4261_;
v___y_4169_ = v___y_4267_;
v___y_4170_ = v___y_4268_;
v___y_4171_ = v___y_4264_;
v___y_4172_ = v___y_4265_;
v___y_4173_ = v_trueEqFalse_4263_;
v___y_4174_ = v___y_4273_;
v___y_4175_ = v___y_4270_;
v___y_4176_ = v___y_4259_;
v___y_4177_ = v___y_4269_;
v___y_4178_ = v___y_4271_;
v___y_4179_ = v_valueInconsistency_4262_;
goto v___jp_4165_;
}
else
{
v___y_4234_ = v___y_4272_;
v___y_4235_ = v___y_4266_;
v___y_4236_ = v___y_4261_;
v___y_4237_ = v___y_4267_;
v___y_4238_ = v___y_4268_;
v___y_4239_ = v___y_4264_;
v___y_4240_ = v___y_4265_;
v___y_4241_ = v_trueEqFalse_4263_;
v___y_4242_ = v___y_4273_;
v___y_4243_ = v___y_4270_;
v___y_4244_ = v___y_4259_;
v___y_4245_ = v___y_4269_;
v___y_4246_ = v___y_4271_;
v___y_4247_ = v_valueInconsistency_4262_;
v___y_4248_ = v___x_4036_;
goto v___jp_4233_;
}
}
}
v___jp_4275_:
{
uint8_t v_interpreted_4290_; 
v_interpreted_4290_ = lean_ctor_get_uint8(v___y_4276_, sizeof(void*)*12 + 1);
v___y_4259_ = v___y_4276_;
v_interpreted_4260_ = v_interpreted_4290_;
v___y_4261_ = v___y_4277_;
v_valueInconsistency_4262_ = v_valueInconsistency_4278_;
v_trueEqFalse_4263_ = v_trueEqFalse_4279_;
v___y_4264_ = v___y_4280_;
v___y_4265_ = v___y_4281_;
v___y_4266_ = v___y_4282_;
v___y_4267_ = v___y_4283_;
v___y_4268_ = v___y_4284_;
v___y_4269_ = v___y_4285_;
v___y_4270_ = v___y_4286_;
v___y_4271_ = v___y_4287_;
v___y_4272_ = v___y_4288_;
v___y_4273_ = v___y_4289_;
goto v___jp_4258_;
}
v___jp_4291_:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4297_, v___y_4298_, v___y_4300_, v___y_4295_, v___y_4301_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_dec_ref(v___x_4304_);
v___y_4276_ = v___y_4299_;
v___y_4277_ = v___y_4296_;
v_valueInconsistency_4278_ = v___x_4036_;
v_trueEqFalse_4279_ = v___x_4040_;
v___y_4280_ = v___y_4297_;
v___y_4281_ = v___y_4292_;
v___y_4282_ = v___y_4302_;
v___y_4283_ = v___y_4294_;
v___y_4284_ = v___y_4303_;
v___y_4285_ = v___y_4293_;
v___y_4286_ = v___y_4298_;
v___y_4287_ = v___y_4300_;
v___y_4288_ = v___y_4295_;
v___y_4289_ = v___y_4301_;
goto v___jp_4275_;
}
else
{
lean_dec_ref(v___y_4299_);
lean_dec_ref(v___y_4296_);
lean_dec(v_a_4033_);
lean_dec(v_a_4030_);
lean_dec_ref(v_proof_4012_);
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
return v___x_4304_;
}
}
v___jp_4305_:
{
if (v___y_4308_ == 0)
{
lean_object* v_self_4319_; uint8_t v_interpreted_4320_; lean_object* v_self_4321_; lean_object* v___x_4322_; 
v_self_4319_ = lean_ctor_get(v___y_4313_, 0);
v_interpreted_4320_ = lean_ctor_get_uint8(v___y_4313_, sizeof(void*)*12 + 1);
v_self_4321_ = lean_ctor_get(v___y_4310_, 0);
lean_inc_ref(v_self_4321_);
lean_inc_ref(v_self_4319_);
v___x_4322_ = l_Lean_Meta_Grind_hasSameType(v_self_4319_, v_self_4321_, v___y_4314_, v___y_4315_, v___y_4311_, v___y_4316_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; uint8_t v___x_4324_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref(v___x_4322_);
v___x_4324_ = lean_unbox(v_a_4323_);
lean_dec(v_a_4323_);
if (v___x_4324_ == 0)
{
v___y_4259_ = v___y_4313_;
v_interpreted_4260_ = v_interpreted_4320_;
v___y_4261_ = v___y_4310_;
v_valueInconsistency_4262_ = v___x_4036_;
v_trueEqFalse_4263_ = v___x_4036_;
v___y_4264_ = v___y_4312_;
v___y_4265_ = v___y_4306_;
v___y_4266_ = v___y_4317_;
v___y_4267_ = v___y_4309_;
v___y_4268_ = v___y_4318_;
v___y_4269_ = v___y_4307_;
v___y_4270_ = v___y_4314_;
v___y_4271_ = v___y_4315_;
v___y_4272_ = v___y_4311_;
v___y_4273_ = v___y_4316_;
goto v___jp_4258_;
}
else
{
v___y_4259_ = v___y_4313_;
v_interpreted_4260_ = v_interpreted_4320_;
v___y_4261_ = v___y_4310_;
v_valueInconsistency_4262_ = v___x_4040_;
v_trueEqFalse_4263_ = v___x_4036_;
v___y_4264_ = v___y_4312_;
v___y_4265_ = v___y_4306_;
v___y_4266_ = v___y_4317_;
v___y_4267_ = v___y_4309_;
v___y_4268_ = v___y_4318_;
v___y_4269_ = v___y_4307_;
v___y_4270_ = v___y_4314_;
v___y_4271_ = v___y_4315_;
v___y_4272_ = v___y_4311_;
v___y_4273_ = v___y_4316_;
goto v___jp_4258_;
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec_ref(v___y_4313_);
lean_dec_ref(v___y_4310_);
lean_dec(v_a_4033_);
lean_dec(v_a_4030_);
lean_dec_ref(v_proof_4012_);
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
v_a_4325_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4322_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4322_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
else
{
v___y_4276_ = v___y_4313_;
v___y_4277_ = v___y_4310_;
v_valueInconsistency_4278_ = v___x_4040_;
v_trueEqFalse_4279_ = v___x_4036_;
v___y_4280_ = v___y_4312_;
v___y_4281_ = v___y_4306_;
v___y_4282_ = v___y_4317_;
v___y_4283_ = v___y_4309_;
v___y_4284_ = v___y_4318_;
v___y_4285_ = v___y_4307_;
v___y_4286_ = v___y_4314_;
v___y_4287_ = v___y_4315_;
v___y_4288_ = v___y_4311_;
v___y_4289_ = v___y_4316_;
goto v___jp_4275_;
}
}
v___jp_4333_:
{
if (v___y_4346_ == 0)
{
v___y_4276_ = v___y_4341_;
v___y_4277_ = v___y_4338_;
v_valueInconsistency_4278_ = v___x_4036_;
v_trueEqFalse_4279_ = v___x_4036_;
v___y_4280_ = v___y_4339_;
v___y_4281_ = v___y_4334_;
v___y_4282_ = v___y_4342_;
v___y_4283_ = v___y_4336_;
v___y_4284_ = v___y_4345_;
v___y_4285_ = v___y_4335_;
v___y_4286_ = v___y_4340_;
v___y_4287_ = v___y_4343_;
v___y_4288_ = v___y_4337_;
v___y_4289_ = v___y_4344_;
goto v___jp_4275_;
}
else
{
uint8_t v___x_4347_; 
lean_inc_ref(v_root_4034_);
v___x_4347_ = l_Lean_Expr_isTrue(v_root_4034_);
if (v___x_4347_ == 0)
{
uint8_t v___x_4348_; 
lean_inc_ref(v_root_4035_);
v___x_4348_ = l_Lean_Expr_isTrue(v_root_4035_);
if (v___x_4348_ == 0)
{
if (v_isHEq_4013_ == 0)
{
uint8_t v_heqProofs_4349_; 
v_heqProofs_4349_ = lean_ctor_get_uint8(v___y_4341_, sizeof(void*)*12 + 4);
if (v_heqProofs_4349_ == 0)
{
uint8_t v_heqProofs_4350_; 
v_heqProofs_4350_ = lean_ctor_get_uint8(v___y_4338_, sizeof(void*)*12 + 4);
if (v_heqProofs_4350_ == 0)
{
uint8_t v_interpreted_4351_; 
v_interpreted_4351_ = lean_ctor_get_uint8(v___y_4341_, sizeof(void*)*12 + 1);
v___y_4259_ = v___y_4341_;
v_interpreted_4260_ = v_interpreted_4351_;
v___y_4261_ = v___y_4338_;
v_valueInconsistency_4262_ = v___x_4040_;
v_trueEqFalse_4263_ = v___x_4036_;
v___y_4264_ = v___y_4339_;
v___y_4265_ = v___y_4334_;
v___y_4266_ = v___y_4342_;
v___y_4267_ = v___y_4336_;
v___y_4268_ = v___y_4345_;
v___y_4269_ = v___y_4335_;
v___y_4270_ = v___y_4340_;
v___y_4271_ = v___y_4343_;
v___y_4272_ = v___y_4337_;
v___y_4273_ = v___y_4344_;
goto v___jp_4258_;
}
else
{
v___y_4306_ = v___y_4334_;
v___y_4307_ = v___y_4335_;
v___y_4308_ = v___x_4348_;
v___y_4309_ = v___y_4336_;
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4337_;
v___y_4312_ = v___y_4339_;
v___y_4313_ = v___y_4341_;
v___y_4314_ = v___y_4340_;
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4344_;
v___y_4317_ = v___y_4342_;
v___y_4318_ = v___y_4345_;
goto v___jp_4305_;
}
}
else
{
v___y_4306_ = v___y_4334_;
v___y_4307_ = v___y_4335_;
v___y_4308_ = v___x_4348_;
v___y_4309_ = v___y_4336_;
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4337_;
v___y_4312_ = v___y_4339_;
v___y_4313_ = v___y_4341_;
v___y_4314_ = v___y_4340_;
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4344_;
v___y_4317_ = v___y_4342_;
v___y_4318_ = v___y_4345_;
goto v___jp_4305_;
}
}
else
{
v___y_4306_ = v___y_4334_;
v___y_4307_ = v___y_4335_;
v___y_4308_ = v___x_4348_;
v___y_4309_ = v___y_4336_;
v___y_4310_ = v___y_4338_;
v___y_4311_ = v___y_4337_;
v___y_4312_ = v___y_4339_;
v___y_4313_ = v___y_4341_;
v___y_4314_ = v___y_4340_;
v___y_4315_ = v___y_4343_;
v___y_4316_ = v___y_4344_;
v___y_4317_ = v___y_4342_;
v___y_4318_ = v___y_4345_;
goto v___jp_4305_;
}
}
else
{
v___y_4292_ = v___y_4334_;
v___y_4293_ = v___y_4335_;
v___y_4294_ = v___y_4336_;
v___y_4295_ = v___y_4337_;
v___y_4296_ = v___y_4338_;
v___y_4297_ = v___y_4339_;
v___y_4298_ = v___y_4340_;
v___y_4299_ = v___y_4341_;
v___y_4300_ = v___y_4343_;
v___y_4301_ = v___y_4344_;
v___y_4302_ = v___y_4342_;
v___y_4303_ = v___y_4345_;
goto v___jp_4291_;
}
}
else
{
v___y_4292_ = v___y_4334_;
v___y_4293_ = v___y_4335_;
v___y_4294_ = v___y_4336_;
v___y_4295_ = v___y_4337_;
v___y_4296_ = v___y_4338_;
v___y_4297_ = v___y_4339_;
v___y_4298_ = v___y_4340_;
v___y_4299_ = v___y_4341_;
v___y_4300_ = v___y_4343_;
v___y_4301_ = v___y_4344_;
v___y_4302_ = v___y_4342_;
v___y_4303_ = v___y_4345_;
goto v___jp_4291_;
}
}
}
v___jp_4352_:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4363_ = lean_st_ref_get(v___y_4353_);
lean_inc_ref(v_root_4034_);
v___x_4364_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4363_, v_root_4034_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
lean_dec(v___x_4363_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref(v___x_4364_);
v___x_4366_ = lean_st_ref_get(v___y_4353_);
lean_inc_ref(v_root_4035_);
v___x_4367_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4366_, v_root_4035_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
lean_dec(v___x_4366_);
if (lean_obj_tag(v___x_4367_) == 0)
{
uint8_t v_interpreted_4368_; 
v_interpreted_4368_ = lean_ctor_get_uint8(v_a_4365_, sizeof(void*)*12 + 1);
if (v_interpreted_4368_ == 0)
{
lean_object* v_a_4369_; 
v_a_4369_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4369_);
lean_dec_ref(v___x_4367_);
v___y_4334_ = v___y_4354_;
v___y_4335_ = v___y_4358_;
v___y_4336_ = v___y_4356_;
v___y_4337_ = v___y_4361_;
v___y_4338_ = v_a_4369_;
v___y_4339_ = v___y_4353_;
v___y_4340_ = v___y_4359_;
v___y_4341_ = v_a_4365_;
v___y_4342_ = v___y_4355_;
v___y_4343_ = v___y_4360_;
v___y_4344_ = v___y_4362_;
v___y_4345_ = v___y_4357_;
v___y_4346_ = v___x_4036_;
goto v___jp_4333_;
}
else
{
lean_object* v_a_4370_; uint8_t v_interpreted_4371_; 
v_a_4370_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4370_);
lean_dec_ref(v___x_4367_);
v_interpreted_4371_ = lean_ctor_get_uint8(v_a_4370_, sizeof(void*)*12 + 1);
v___y_4334_ = v___y_4354_;
v___y_4335_ = v___y_4358_;
v___y_4336_ = v___y_4356_;
v___y_4337_ = v___y_4361_;
v___y_4338_ = v_a_4370_;
v___y_4339_ = v___y_4353_;
v___y_4340_ = v___y_4359_;
v___y_4341_ = v_a_4365_;
v___y_4342_ = v___y_4355_;
v___y_4343_ = v___y_4360_;
v___y_4344_ = v___y_4362_;
v___y_4345_ = v___y_4357_;
v___y_4346_ = v_interpreted_4371_;
goto v___jp_4333_;
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec(v_a_4365_);
lean_dec(v_a_4033_);
lean_dec(v_a_4030_);
lean_dec_ref(v_proof_4012_);
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
v_a_4372_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4367_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4367_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_a_4033_);
lean_dec(v_a_4030_);
lean_dec_ref(v_proof_4012_);
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
v_a_4380_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4364_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4364_);
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
}
else
{
lean_object* v_options_4407_; uint8_t v_hasTrace_4408_; 
lean_dec(v_a_4033_);
lean_dec(v_a_4030_);
lean_dec_ref(v_proof_4012_);
v_options_4407_ = lean_ctor_get(v_a_4022_, 2);
v_hasTrace_4408_ = lean_ctor_get_uint8(v_options_4407_, sizeof(void*)*1);
if (v_hasTrace_4408_ == 0)
{
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
goto v___jp_4025_;
}
else
{
lean_object* v_inheritedTraceOptions_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; uint8_t v___x_4412_; 
v_inheritedTraceOptions_4409_ = lean_ctor_get(v_a_4022_, 13);
v___x_4410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4411_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4412_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4409_, v_options_4407_, v___x_4411_);
if (v___x_4412_ == 0)
{
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
goto v___jp_4025_;
}
else
{
lean_object* v___x_4413_; 
v___x_4413_ = l_Lean_Meta_Grind_updateLastTag(v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v___x_4414_; 
lean_dec_ref(v___x_4413_);
v___x_4414_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4010_, v_a_4014_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4416_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_a_4415_);
lean_dec_ref(v___x_4414_);
v___x_4416_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4011_, v_a_4014_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4417_);
lean_dec_ref(v___x_4416_);
v___x_4418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4419_, 0, v_a_4415_);
lean_ctor_set(v___x_4419_, 1, v___x_4418_);
v___x_4420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
lean_ctor_set(v___x_4420_, 1, v_a_4417_);
v___x_4421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4420_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
v___x_4423_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4410_, v___x_4422_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_dec_ref(v___x_4423_);
goto v___jp_4025_;
}
else
{
return v___x_4423_;
}
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_a_4415_);
v_a_4424_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4416_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4416_);
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
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec_ref(v_rhs_4011_);
v_a_4432_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4414_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4414_);
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
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
return v___x_4413_;
}
}
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_dec(v_a_4030_);
lean_dec_ref(v_proof_4012_);
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
v_a_4440_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4032_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4032_);
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
}
else
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4455_; 
lean_dec_ref(v_proof_4012_);
lean_dec_ref(v_rhs_4011_);
lean_dec_ref(v_lhs_4010_);
v_a_4448_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4450_ = v___x_4029_;
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4029_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
}
v___jp_4025_:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4026_ = lean_box(0);
v___x_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
return v___x_4027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4456_, lean_object* v_rhs_4457_, lean_object* v_proof_4458_, lean_object* v_isHEq_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
uint8_t v_isHEq_boxed_4471_; lean_object* v_res_4472_; 
v_isHEq_boxed_4471_ = lean_unbox(v_isHEq_4459_);
v_res_4472_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4456_, v_rhs_4457_, v_proof_4458_, v_isHEq_boxed_4471_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
lean_dec(v_a_4463_);
lean_dec_ref(v_a_4462_);
lean_dec(v_a_4461_);
lean_dec(v_a_4460_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4475_){
_start:
{
lean_object* v___x_4477_; lean_object* v_toGoalState_4478_; lean_object* v_mvarId_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4515_; 
v___x_4477_ = lean_st_ref_take(v_a_4475_);
v_toGoalState_4478_ = lean_ctor_get(v___x_4477_, 0);
v_mvarId_4479_ = lean_ctor_get(v___x_4477_, 1);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4481_ = v___x_4477_;
v_isShared_4482_ = v_isSharedCheck_4515_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_mvarId_4479_);
lean_inc(v_toGoalState_4478_);
lean_dec(v___x_4477_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4515_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v_nextDeclIdx_4483_; lean_object* v_enodeMap_4484_; lean_object* v_exprs_4485_; lean_object* v_parents_4486_; lean_object* v_congrTable_4487_; lean_object* v_appMap_4488_; lean_object* v_indicesFound_4489_; uint8_t v_inconsistent_4490_; lean_object* v_nextIdx_4491_; lean_object* v_newRawFacts_4492_; lean_object* v_facts_4493_; lean_object* v_extThms_4494_; lean_object* v_ematch_4495_; lean_object* v_inj_4496_; lean_object* v_split_4497_; lean_object* v_clean_4498_; lean_object* v_sstates_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4513_; 
v_nextDeclIdx_4483_ = lean_ctor_get(v_toGoalState_4478_, 0);
v_enodeMap_4484_ = lean_ctor_get(v_toGoalState_4478_, 1);
v_exprs_4485_ = lean_ctor_get(v_toGoalState_4478_, 2);
v_parents_4486_ = lean_ctor_get(v_toGoalState_4478_, 3);
v_congrTable_4487_ = lean_ctor_get(v_toGoalState_4478_, 4);
v_appMap_4488_ = lean_ctor_get(v_toGoalState_4478_, 5);
v_indicesFound_4489_ = lean_ctor_get(v_toGoalState_4478_, 6);
v_inconsistent_4490_ = lean_ctor_get_uint8(v_toGoalState_4478_, sizeof(void*)*17);
v_nextIdx_4491_ = lean_ctor_get(v_toGoalState_4478_, 8);
v_newRawFacts_4492_ = lean_ctor_get(v_toGoalState_4478_, 9);
v_facts_4493_ = lean_ctor_get(v_toGoalState_4478_, 10);
v_extThms_4494_ = lean_ctor_get(v_toGoalState_4478_, 11);
v_ematch_4495_ = lean_ctor_get(v_toGoalState_4478_, 12);
v_inj_4496_ = lean_ctor_get(v_toGoalState_4478_, 13);
v_split_4497_ = lean_ctor_get(v_toGoalState_4478_, 14);
v_clean_4498_ = lean_ctor_get(v_toGoalState_4478_, 15);
v_sstates_4499_ = lean_ctor_get(v_toGoalState_4478_, 16);
v_isSharedCheck_4513_ = !lean_is_exclusive(v_toGoalState_4478_);
if (v_isSharedCheck_4513_ == 0)
{
lean_object* v_unused_4514_; 
v_unused_4514_ = lean_ctor_get(v_toGoalState_4478_, 7);
lean_dec(v_unused_4514_);
v___x_4501_ = v_toGoalState_4478_;
v_isShared_4502_ = v_isSharedCheck_4513_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_sstates_4499_);
lean_inc(v_clean_4498_);
lean_inc(v_split_4497_);
lean_inc(v_inj_4496_);
lean_inc(v_ematch_4495_);
lean_inc(v_extThms_4494_);
lean_inc(v_facts_4493_);
lean_inc(v_newRawFacts_4492_);
lean_inc(v_nextIdx_4491_);
lean_inc(v_indicesFound_4489_);
lean_inc(v_appMap_4488_);
lean_inc(v_congrTable_4487_);
lean_inc(v_parents_4486_);
lean_inc(v_exprs_4485_);
lean_inc(v_enodeMap_4484_);
lean_inc(v_nextDeclIdx_4483_);
lean_dec(v_toGoalState_4478_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4513_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v___x_4503_; lean_object* v___x_4505_; 
v___x_4503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 7, v___x_4503_);
v___x_4505_ = v___x_4501_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_nextDeclIdx_4483_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_enodeMap_4484_);
lean_ctor_set(v_reuseFailAlloc_4512_, 2, v_exprs_4485_);
lean_ctor_set(v_reuseFailAlloc_4512_, 3, v_parents_4486_);
lean_ctor_set(v_reuseFailAlloc_4512_, 4, v_congrTable_4487_);
lean_ctor_set(v_reuseFailAlloc_4512_, 5, v_appMap_4488_);
lean_ctor_set(v_reuseFailAlloc_4512_, 6, v_indicesFound_4489_);
lean_ctor_set(v_reuseFailAlloc_4512_, 7, v___x_4503_);
lean_ctor_set(v_reuseFailAlloc_4512_, 8, v_nextIdx_4491_);
lean_ctor_set(v_reuseFailAlloc_4512_, 9, v_newRawFacts_4492_);
lean_ctor_set(v_reuseFailAlloc_4512_, 10, v_facts_4493_);
lean_ctor_set(v_reuseFailAlloc_4512_, 11, v_extThms_4494_);
lean_ctor_set(v_reuseFailAlloc_4512_, 12, v_ematch_4495_);
lean_ctor_set(v_reuseFailAlloc_4512_, 13, v_inj_4496_);
lean_ctor_set(v_reuseFailAlloc_4512_, 14, v_split_4497_);
lean_ctor_set(v_reuseFailAlloc_4512_, 15, v_clean_4498_);
lean_ctor_set(v_reuseFailAlloc_4512_, 16, v_sstates_4499_);
lean_ctor_set_uint8(v_reuseFailAlloc_4512_, sizeof(void*)*17, v_inconsistent_4490_);
v___x_4505_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4507_; 
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 0, v___x_4505_);
v___x_4507_ = v___x_4481_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4505_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_mvarId_4479_);
v___x_4507_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4508_ = lean_st_ref_set(v_a_4475_, v___x_4507_);
v___x_4509_ = lean_box(0);
v___x_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
return v___x_4510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4516_);
lean_dec(v_a_4516_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v___x_4530_; 
v___x_4530_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4519_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec(v_a_4532_);
lean_dec(v_a_4531_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4543_){
_start:
{
lean_object* v___x_4545_; lean_object* v_toGoalState_4546_; lean_object* v_newFacts_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; uint8_t v___x_4551_; 
v___x_4545_ = lean_st_ref_get(v_a_4543_);
v_toGoalState_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc_ref(v_toGoalState_4546_);
lean_dec(v___x_4545_);
v_newFacts_4547_ = lean_ctor_get(v_toGoalState_4546_, 7);
lean_inc_ref(v_newFacts_4547_);
lean_dec_ref(v_toGoalState_4546_);
v___x_4548_ = lean_array_get_size(v_newFacts_4547_);
v___x_4549_ = lean_unsigned_to_nat(1u);
v___x_4550_ = lean_nat_sub(v___x_4548_, v___x_4549_);
v___x_4551_ = lean_nat_dec_lt(v___x_4550_, v___x_4548_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
lean_dec(v___x_4550_);
lean_dec_ref(v_newFacts_4547_);
v___x_4552_ = lean_box(0);
v___x_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
return v___x_4553_;
}
else
{
lean_object* v___x_4554_; lean_object* v_toGoalState_4555_; lean_object* v_mvarId_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4593_; 
v___x_4554_ = lean_st_ref_take(v_a_4543_);
v_toGoalState_4555_ = lean_ctor_get(v___x_4554_, 0);
v_mvarId_4556_ = lean_ctor_get(v___x_4554_, 1);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4558_ = v___x_4554_;
v_isShared_4559_ = v_isSharedCheck_4593_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_mvarId_4556_);
lean_inc(v_toGoalState_4555_);
lean_dec(v___x_4554_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4593_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v_nextDeclIdx_4560_; lean_object* v_enodeMap_4561_; lean_object* v_exprs_4562_; lean_object* v_parents_4563_; lean_object* v_congrTable_4564_; lean_object* v_appMap_4565_; lean_object* v_indicesFound_4566_; lean_object* v_newFacts_4567_; uint8_t v_inconsistent_4568_; lean_object* v_nextIdx_4569_; lean_object* v_newRawFacts_4570_; lean_object* v_facts_4571_; lean_object* v_extThms_4572_; lean_object* v_ematch_4573_; lean_object* v_inj_4574_; lean_object* v_split_4575_; lean_object* v_clean_4576_; lean_object* v_sstates_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4592_; 
v_nextDeclIdx_4560_ = lean_ctor_get(v_toGoalState_4555_, 0);
v_enodeMap_4561_ = lean_ctor_get(v_toGoalState_4555_, 1);
v_exprs_4562_ = lean_ctor_get(v_toGoalState_4555_, 2);
v_parents_4563_ = lean_ctor_get(v_toGoalState_4555_, 3);
v_congrTable_4564_ = lean_ctor_get(v_toGoalState_4555_, 4);
v_appMap_4565_ = lean_ctor_get(v_toGoalState_4555_, 5);
v_indicesFound_4566_ = lean_ctor_get(v_toGoalState_4555_, 6);
v_newFacts_4567_ = lean_ctor_get(v_toGoalState_4555_, 7);
v_inconsistent_4568_ = lean_ctor_get_uint8(v_toGoalState_4555_, sizeof(void*)*17);
v_nextIdx_4569_ = lean_ctor_get(v_toGoalState_4555_, 8);
v_newRawFacts_4570_ = lean_ctor_get(v_toGoalState_4555_, 9);
v_facts_4571_ = lean_ctor_get(v_toGoalState_4555_, 10);
v_extThms_4572_ = lean_ctor_get(v_toGoalState_4555_, 11);
v_ematch_4573_ = lean_ctor_get(v_toGoalState_4555_, 12);
v_inj_4574_ = lean_ctor_get(v_toGoalState_4555_, 13);
v_split_4575_ = lean_ctor_get(v_toGoalState_4555_, 14);
v_clean_4576_ = lean_ctor_get(v_toGoalState_4555_, 15);
v_sstates_4577_ = lean_ctor_get(v_toGoalState_4555_, 16);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_toGoalState_4555_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4579_ = v_toGoalState_4555_;
v_isShared_4580_ = v_isSharedCheck_4592_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_sstates_4577_);
lean_inc(v_clean_4576_);
lean_inc(v_split_4575_);
lean_inc(v_inj_4574_);
lean_inc(v_ematch_4573_);
lean_inc(v_extThms_4572_);
lean_inc(v_facts_4571_);
lean_inc(v_newRawFacts_4570_);
lean_inc(v_nextIdx_4569_);
lean_inc(v_newFacts_4567_);
lean_inc(v_indicesFound_4566_);
lean_inc(v_appMap_4565_);
lean_inc(v_congrTable_4564_);
lean_inc(v_parents_4563_);
lean_inc(v_exprs_4562_);
lean_inc(v_enodeMap_4561_);
lean_inc(v_nextDeclIdx_4560_);
lean_dec(v_toGoalState_4555_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4592_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4581_; lean_object* v___x_4583_; 
v___x_4581_ = lean_array_pop(v_newFacts_4567_);
if (v_isShared_4580_ == 0)
{
lean_ctor_set(v___x_4579_, 7, v___x_4581_);
v___x_4583_ = v___x_4579_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_nextDeclIdx_4560_);
lean_ctor_set(v_reuseFailAlloc_4591_, 1, v_enodeMap_4561_);
lean_ctor_set(v_reuseFailAlloc_4591_, 2, v_exprs_4562_);
lean_ctor_set(v_reuseFailAlloc_4591_, 3, v_parents_4563_);
lean_ctor_set(v_reuseFailAlloc_4591_, 4, v_congrTable_4564_);
lean_ctor_set(v_reuseFailAlloc_4591_, 5, v_appMap_4565_);
lean_ctor_set(v_reuseFailAlloc_4591_, 6, v_indicesFound_4566_);
lean_ctor_set(v_reuseFailAlloc_4591_, 7, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4591_, 8, v_nextIdx_4569_);
lean_ctor_set(v_reuseFailAlloc_4591_, 9, v_newRawFacts_4570_);
lean_ctor_set(v_reuseFailAlloc_4591_, 10, v_facts_4571_);
lean_ctor_set(v_reuseFailAlloc_4591_, 11, v_extThms_4572_);
lean_ctor_set(v_reuseFailAlloc_4591_, 12, v_ematch_4573_);
lean_ctor_set(v_reuseFailAlloc_4591_, 13, v_inj_4574_);
lean_ctor_set(v_reuseFailAlloc_4591_, 14, v_split_4575_);
lean_ctor_set(v_reuseFailAlloc_4591_, 15, v_clean_4576_);
lean_ctor_set(v_reuseFailAlloc_4591_, 16, v_sstates_4577_);
lean_ctor_set_uint8(v_reuseFailAlloc_4591_, sizeof(void*)*17, v_inconsistent_4568_);
v___x_4583_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4585_; 
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 0, v___x_4583_);
v___x_4585_ = v___x_4558_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4583_);
lean_ctor_set(v_reuseFailAlloc_4590_, 1, v_mvarId_4556_);
v___x_4585_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4586_ = lean_st_ref_set(v_a_4543_, v___x_4585_);
v___x_4587_ = lean_array_fget(v_newFacts_4547_, v___x_4550_);
lean_dec(v___x_4550_);
lean_dec_ref(v_newFacts_4547_);
v___x_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
return v___x_4589_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4594_);
lean_dec(v_a_4594_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v___x_4608_; 
v___x_4608_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4597_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
lean_dec(v_a_4610_);
lean_dec(v_a_4609_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4621_, lean_object* v_rhs_4622_, lean_object* v_proof_4623_, uint8_t v_isHEq_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_){
_start:
{
lean_object* v___x_4636_; 
v___x_4636_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4621_, v_rhs_4622_, v_proof_4623_, v_isHEq_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v___x_4637_; 
lean_dec_ref(v___x_4636_);
lean_inc(v_a_4634_);
lean_inc_ref(v_a_4633_);
lean_inc(v_a_4632_);
lean_inc_ref(v_a_4631_);
lean_inc(v_a_4630_);
lean_inc_ref(v_a_4629_);
lean_inc(v_a_4628_);
lean_inc_ref(v_a_4627_);
lean_inc(v_a_4626_);
lean_inc(v_a_4625_);
v___x_4637_ = lean_grind_process_new_facts(v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_);
return v___x_4637_;
}
else
{
return v___x_4636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4638_, lean_object* v_rhs_4639_, lean_object* v_proof_4640_, lean_object* v_isHEq_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
uint8_t v_isHEq_boxed_4653_; lean_object* v_res_4654_; 
v_isHEq_boxed_4653_ = lean_unbox(v_isHEq_4641_);
v_res_4654_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4638_, v_rhs_4639_, v_proof_4640_, v_isHEq_boxed_4653_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
lean_dec(v_a_4651_);
lean_dec_ref(v_a_4650_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec(v_a_4642_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4655_, lean_object* v_rhs_4656_, lean_object* v_proof_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
uint8_t v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = 0;
v___x_4670_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4655_, v_rhs_4656_, v_proof_4657_, v___x_4669_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4671_, lean_object* v_rhs_4672_, lean_object* v_proof_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4671_, v_rhs_4672_, v_proof_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4686_, lean_object* v_rhs_4687_, lean_object* v_proof_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_){
_start:
{
uint8_t v___x_4700_; lean_object* v___x_4701_; 
v___x_4700_ = 1;
v___x_4701_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4686_, v_rhs_4687_, v_proof_4688_, v___x_4700_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_);
return v___x_4701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4702_, lean_object* v_rhs_4703_, lean_object* v_proof_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4702_, v_rhs_4703_, v_proof_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_);
lean_dec(v_a_4714_);
lean_dec_ref(v_a_4713_);
lean_dec(v_a_4712_);
lean_dec_ref(v_a_4711_);
lean_dec(v_a_4710_);
lean_dec_ref(v_a_4709_);
lean_dec(v_a_4708_);
lean_dec_ref(v_a_4707_);
lean_dec(v_a_4706_);
lean_dec(v_a_4705_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4717_, lean_object* v_a_4718_){
_start:
{
lean_object* v___x_4720_; lean_object* v_toGoalState_4721_; lean_object* v_mvarId_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4758_; 
v___x_4720_ = lean_st_ref_take(v_a_4718_);
v_toGoalState_4721_ = lean_ctor_get(v___x_4720_, 0);
v_mvarId_4722_ = lean_ctor_get(v___x_4720_, 1);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4724_ = v___x_4720_;
v_isShared_4725_ = v_isSharedCheck_4758_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_mvarId_4722_);
lean_inc(v_toGoalState_4721_);
lean_dec(v___x_4720_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4758_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v_nextDeclIdx_4726_; lean_object* v_enodeMap_4727_; lean_object* v_exprs_4728_; lean_object* v_parents_4729_; lean_object* v_congrTable_4730_; lean_object* v_appMap_4731_; lean_object* v_indicesFound_4732_; lean_object* v_newFacts_4733_; uint8_t v_inconsistent_4734_; lean_object* v_nextIdx_4735_; lean_object* v_newRawFacts_4736_; lean_object* v_facts_4737_; lean_object* v_extThms_4738_; lean_object* v_ematch_4739_; lean_object* v_inj_4740_; lean_object* v_split_4741_; lean_object* v_clean_4742_; lean_object* v_sstates_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4757_; 
v_nextDeclIdx_4726_ = lean_ctor_get(v_toGoalState_4721_, 0);
v_enodeMap_4727_ = lean_ctor_get(v_toGoalState_4721_, 1);
v_exprs_4728_ = lean_ctor_get(v_toGoalState_4721_, 2);
v_parents_4729_ = lean_ctor_get(v_toGoalState_4721_, 3);
v_congrTable_4730_ = lean_ctor_get(v_toGoalState_4721_, 4);
v_appMap_4731_ = lean_ctor_get(v_toGoalState_4721_, 5);
v_indicesFound_4732_ = lean_ctor_get(v_toGoalState_4721_, 6);
v_newFacts_4733_ = lean_ctor_get(v_toGoalState_4721_, 7);
v_inconsistent_4734_ = lean_ctor_get_uint8(v_toGoalState_4721_, sizeof(void*)*17);
v_nextIdx_4735_ = lean_ctor_get(v_toGoalState_4721_, 8);
v_newRawFacts_4736_ = lean_ctor_get(v_toGoalState_4721_, 9);
v_facts_4737_ = lean_ctor_get(v_toGoalState_4721_, 10);
v_extThms_4738_ = lean_ctor_get(v_toGoalState_4721_, 11);
v_ematch_4739_ = lean_ctor_get(v_toGoalState_4721_, 12);
v_inj_4740_ = lean_ctor_get(v_toGoalState_4721_, 13);
v_split_4741_ = lean_ctor_get(v_toGoalState_4721_, 14);
v_clean_4742_ = lean_ctor_get(v_toGoalState_4721_, 15);
v_sstates_4743_ = lean_ctor_get(v_toGoalState_4721_, 16);
v_isSharedCheck_4757_ = !lean_is_exclusive(v_toGoalState_4721_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4745_ = v_toGoalState_4721_;
v_isShared_4746_ = v_isSharedCheck_4757_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_sstates_4743_);
lean_inc(v_clean_4742_);
lean_inc(v_split_4741_);
lean_inc(v_inj_4740_);
lean_inc(v_ematch_4739_);
lean_inc(v_extThms_4738_);
lean_inc(v_facts_4737_);
lean_inc(v_newRawFacts_4736_);
lean_inc(v_nextIdx_4735_);
lean_inc(v_newFacts_4733_);
lean_inc(v_indicesFound_4732_);
lean_inc(v_appMap_4731_);
lean_inc(v_congrTable_4730_);
lean_inc(v_parents_4729_);
lean_inc(v_exprs_4728_);
lean_inc(v_enodeMap_4727_);
lean_inc(v_nextDeclIdx_4726_);
lean_dec(v_toGoalState_4721_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4757_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4747_; lean_object* v___x_4749_; 
v___x_4747_ = l_Lean_PersistentArray_push___redArg(v_facts_4737_, v_fact_4717_);
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 10, v___x_4747_);
v___x_4749_ = v___x_4745_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_nextDeclIdx_4726_);
lean_ctor_set(v_reuseFailAlloc_4756_, 1, v_enodeMap_4727_);
lean_ctor_set(v_reuseFailAlloc_4756_, 2, v_exprs_4728_);
lean_ctor_set(v_reuseFailAlloc_4756_, 3, v_parents_4729_);
lean_ctor_set(v_reuseFailAlloc_4756_, 4, v_congrTable_4730_);
lean_ctor_set(v_reuseFailAlloc_4756_, 5, v_appMap_4731_);
lean_ctor_set(v_reuseFailAlloc_4756_, 6, v_indicesFound_4732_);
lean_ctor_set(v_reuseFailAlloc_4756_, 7, v_newFacts_4733_);
lean_ctor_set(v_reuseFailAlloc_4756_, 8, v_nextIdx_4735_);
lean_ctor_set(v_reuseFailAlloc_4756_, 9, v_newRawFacts_4736_);
lean_ctor_set(v_reuseFailAlloc_4756_, 10, v___x_4747_);
lean_ctor_set(v_reuseFailAlloc_4756_, 11, v_extThms_4738_);
lean_ctor_set(v_reuseFailAlloc_4756_, 12, v_ematch_4739_);
lean_ctor_set(v_reuseFailAlloc_4756_, 13, v_inj_4740_);
lean_ctor_set(v_reuseFailAlloc_4756_, 14, v_split_4741_);
lean_ctor_set(v_reuseFailAlloc_4756_, 15, v_clean_4742_);
lean_ctor_set(v_reuseFailAlloc_4756_, 16, v_sstates_4743_);
lean_ctor_set_uint8(v_reuseFailAlloc_4756_, sizeof(void*)*17, v_inconsistent_4734_);
v___x_4749_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4751_; 
if (v_isShared_4725_ == 0)
{
lean_ctor_set(v___x_4724_, 0, v___x_4749_);
v___x_4751_ = v___x_4724_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4749_);
lean_ctor_set(v_reuseFailAlloc_4755_, 1, v_mvarId_4722_);
v___x_4751_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4752_ = lean_st_ref_set(v_a_4718_, v___x_4751_);
v___x_4753_ = lean_box(0);
v___x_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
return v___x_4754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4759_, v_a_4760_);
lean_dec(v_a_4760_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4763_, v_a_4764_);
return v___x_4775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
lean_dec(v_a_4786_);
lean_dec_ref(v_a_4785_);
lean_dec(v_a_4784_);
lean_dec_ref(v_a_4783_);
lean_dec(v_a_4782_);
lean_dec_ref(v_a_4781_);
lean_dec(v_a_4780_);
lean_dec_ref(v_a_4779_);
lean_dec(v_a_4778_);
lean_dec(v_a_4777_);
return v_res_4788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4789_, lean_object* v_rhs_4790_, lean_object* v_proof_4791_, lean_object* v_generation_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_){
_start:
{
lean_object* v___x_4804_; 
lean_inc_ref(v_rhs_4790_);
lean_inc_ref(v_lhs_4789_);
v___x_4804_ = l_Lean_Meta_mkEq(v_lhs_4789_, v_rhs_4790_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4816_; 
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc_n(v_a_4805_, 2);
lean_dec_ref(v___x_4804_);
v___x_4806_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4805_, v_a_4793_);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4816_ == 0)
{
lean_object* v_unused_4817_; 
v_unused_4817_ = lean_ctor_get(v___x_4806_, 0);
lean_dec(v_unused_4817_);
v___x_4808_ = v___x_4806_;
v_isShared_4809_ = v_isSharedCheck_4816_;
goto v_resetjp_4807_;
}
else
{
lean_dec(v___x_4806_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4816_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
if (v_isShared_4809_ == 0)
{
lean_ctor_set_tag(v___x_4808_, 1);
lean_ctor_set(v___x_4808_, 0, v_a_4805_);
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_a_4805_);
v___x_4811_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
lean_object* v___x_4812_; 
lean_inc(v_a_4802_);
lean_inc_ref(v_a_4801_);
lean_inc(v_a_4800_);
lean_inc_ref(v_a_4799_);
lean_inc(v_a_4798_);
lean_inc_ref(v_a_4797_);
lean_inc(v_a_4796_);
lean_inc_ref(v_a_4795_);
lean_inc(v_a_4794_);
lean_inc(v_a_4793_);
lean_inc_ref(v___x_4811_);
lean_inc(v_generation_4792_);
lean_inc_ref(v_lhs_4789_);
v___x_4812_ = lean_grind_internalize(v_lhs_4789_, v_generation_4792_, v___x_4811_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v___x_4813_; 
lean_dec_ref(v___x_4812_);
lean_inc(v_a_4802_);
lean_inc_ref(v_a_4801_);
lean_inc(v_a_4800_);
lean_inc_ref(v_a_4799_);
lean_inc(v_a_4798_);
lean_inc_ref(v_a_4797_);
lean_inc(v_a_4796_);
lean_inc_ref(v_a_4795_);
lean_inc(v_a_4794_);
lean_inc(v_a_4793_);
lean_inc_ref(v_rhs_4790_);
v___x_4813_ = lean_grind_internalize(v_rhs_4790_, v_generation_4792_, v___x_4811_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v___x_4814_; 
lean_dec_ref(v___x_4813_);
v___x_4814_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4789_, v_rhs_4790_, v_proof_4791_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_);
return v___x_4814_;
}
else
{
lean_dec_ref(v_proof_4791_);
lean_dec_ref(v_rhs_4790_);
lean_dec_ref(v_lhs_4789_);
return v___x_4813_;
}
}
else
{
lean_dec_ref(v___x_4811_);
lean_dec(v_generation_4792_);
lean_dec_ref(v_proof_4791_);
lean_dec_ref(v_rhs_4790_);
lean_dec_ref(v_lhs_4789_);
return v___x_4812_;
}
}
}
}
else
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
lean_dec(v_generation_4792_);
lean_dec_ref(v_proof_4791_);
lean_dec_ref(v_rhs_4790_);
lean_dec_ref(v_lhs_4789_);
v_a_4818_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4804_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4804_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4826_, lean_object* v_rhs_4827_, lean_object* v_proof_4828_, lean_object* v_generation_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4826_, v_rhs_4827_, v_proof_4828_, v_generation_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
lean_dec(v_a_4837_);
lean_dec_ref(v_a_4836_);
lean_dec(v_a_4835_);
lean_dec_ref(v_a_4834_);
lean_dec(v_a_4833_);
lean_dec_ref(v_a_4832_);
lean_dec(v_a_4831_);
lean_dec(v_a_4830_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4842_, lean_object* v_generation_4843_, lean_object* v_p_4844_, uint8_t v_isNeg_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4857_ = lean_box(0);
lean_inc(v_a_4855_);
lean_inc_ref(v_a_4854_);
lean_inc(v_a_4853_);
lean_inc_ref(v_a_4852_);
lean_inc(v_a_4851_);
lean_inc_ref(v_a_4850_);
lean_inc(v_a_4849_);
lean_inc_ref(v_a_4848_);
lean_inc(v_a_4847_);
lean_inc(v_a_4846_);
lean_inc_ref(v_p_4844_);
v___x_4858_ = lean_grind_internalize(v_p_4844_, v_generation_4843_, v___x_4857_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_dec_ref(v___x_4858_);
if (v_isNeg_4845_ == 0)
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4850_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; lean_object* v___x_4861_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
lean_inc(v_a_4860_);
lean_dec_ref(v___x_4859_);
v___x_4861_ = l_Lean_Meta_mkEqTrue(v_proof_4842_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4863_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4862_);
lean_dec_ref(v___x_4861_);
v___x_4863_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4844_, v_a_4860_, v_a_4862_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
return v___x_4863_;
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4871_; 
lean_dec(v_a_4860_);
lean_dec_ref(v_p_4844_);
v_a_4864_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4866_ = v___x_4861_;
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4861_);
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
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
lean_dec_ref(v_p_4844_);
lean_dec_ref(v_proof_4842_);
v_a_4872_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4859_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4859_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
else
{
lean_object* v___x_4880_; 
v___x_4880_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4850_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4882_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_a_4881_);
lean_dec_ref(v___x_4880_);
v___x_4882_ = l_Lean_Meta_mkEqFalse(v_proof_4842_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4884_; 
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
lean_inc(v_a_4883_);
lean_dec_ref(v___x_4882_);
v___x_4884_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4844_, v_a_4881_, v_a_4883_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
return v___x_4884_;
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
lean_dec(v_a_4881_);
lean_dec_ref(v_p_4844_);
v_a_4885_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4882_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4882_);
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
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
lean_dec_ref(v_p_4844_);
lean_dec_ref(v_proof_4842_);
v_a_4893_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4880_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4880_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4844_);
lean_dec_ref(v_proof_4842_);
return v___x_4858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4901_, lean_object* v_generation_4902_, lean_object* v_p_4903_, lean_object* v_isNeg_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
uint8_t v_isNeg_boxed_4916_; lean_object* v_res_4917_; 
v_isNeg_boxed_4916_ = lean_unbox(v_isNeg_4904_);
v_res_4917_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4901_, v_generation_4902_, v_p_4903_, v_isNeg_boxed_4916_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
lean_dec(v_a_4912_);
lean_dec_ref(v_a_4911_);
lean_dec(v_a_4910_);
lean_dec_ref(v_a_4909_);
lean_dec(v_a_4908_);
lean_dec_ref(v_a_4907_);
lean_dec(v_a_4906_);
lean_dec(v_a_4905_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4918_, lean_object* v_generation_4919_, lean_object* v_p_4920_, lean_object* v_lhs_4921_, lean_object* v_rhs_4922_, uint8_t v_isNeg_4923_, uint8_t v_isHEq_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
if (v_isNeg_4923_ == 0)
{
lean_object* v___x_4936_; lean_object* v___x_4937_; 
lean_inc_ref(v_p_4920_);
v___x_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4936_, 0, v_p_4920_);
lean_inc(v_a_4934_);
lean_inc_ref(v_a_4933_);
lean_inc(v_a_4932_);
lean_inc_ref(v_a_4931_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc(v_a_4925_);
lean_inc_ref(v___x_4936_);
lean_inc(v_generation_4919_);
lean_inc_ref(v_lhs_4921_);
v___x_4937_ = lean_grind_internalize(v_lhs_4921_, v_generation_4919_, v___x_4936_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_object* v___x_4938_; 
lean_dec_ref(v___x_4937_);
lean_inc(v_a_4934_);
lean_inc_ref(v_a_4933_);
lean_inc(v_a_4932_);
lean_inc_ref(v_a_4931_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc(v_a_4925_);
lean_inc_ref(v_rhs_4922_);
v___x_4938_ = lean_grind_internalize(v_rhs_4922_, v_generation_4919_, v___x_4936_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
lean_dec_ref(v___x_4938_);
v___x_4939_ = lean_box(0);
v___x_4940_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4920_, v___x_4939_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v___x_4941_; 
lean_dec_ref(v___x_4940_);
v___x_4941_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4921_, v_rhs_4922_, v_proof_4918_, v_isHEq_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
return v___x_4941_;
}
else
{
lean_dec_ref(v_rhs_4922_);
lean_dec_ref(v_lhs_4921_);
lean_dec_ref(v_proof_4918_);
return v___x_4940_;
}
}
else
{
lean_dec_ref(v_rhs_4922_);
lean_dec_ref(v_lhs_4921_);
lean_dec_ref(v_p_4920_);
lean_dec_ref(v_proof_4918_);
return v___x_4938_;
}
}
else
{
lean_dec_ref(v___x_4936_);
lean_dec_ref(v_rhs_4922_);
lean_dec_ref(v_lhs_4921_);
lean_dec_ref(v_p_4920_);
lean_dec(v_generation_4919_);
lean_dec_ref(v_proof_4918_);
return v___x_4937_;
}
}
else
{
lean_object* v___x_4942_; lean_object* v___x_4943_; 
lean_dec_ref(v_rhs_4922_);
lean_dec_ref(v_lhs_4921_);
v___x_4942_ = lean_box(0);
lean_inc(v_a_4934_);
lean_inc_ref(v_a_4933_);
lean_inc(v_a_4932_);
lean_inc_ref(v_a_4931_);
lean_inc(v_a_4930_);
lean_inc_ref(v_a_4929_);
lean_inc(v_a_4928_);
lean_inc_ref(v_a_4927_);
lean_inc(v_a_4926_);
lean_inc(v_a_4925_);
lean_inc_ref(v_p_4920_);
v___x_4943_ = lean_grind_internalize(v_p_4920_, v_generation_4919_, v___x_4942_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v___x_4944_; 
lean_dec_ref(v___x_4943_);
v___x_4944_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4929_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4946_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc(v_a_4945_);
lean_dec_ref(v___x_4944_);
v___x_4946_ = l_Lean_Meta_mkEqFalse(v_proof_4918_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v_a_4947_; lean_object* v___x_4948_; 
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
lean_inc(v_a_4947_);
lean_dec_ref(v___x_4946_);
v___x_4948_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4920_, v_a_4945_, v_a_4947_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
return v___x_4948_;
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
lean_dec(v_a_4945_);
lean_dec_ref(v_p_4920_);
v_a_4949_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4946_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4946_);
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
lean_object* v_a_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4964_; 
lean_dec_ref(v_p_4920_);
lean_dec_ref(v_proof_4918_);
v_a_4957_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4959_ = v___x_4944_;
v_isShared_4960_ = v_isSharedCheck_4964_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_a_4957_);
lean_dec(v___x_4944_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4964_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v___x_4962_; 
if (v_isShared_4960_ == 0)
{
v___x_4962_ = v___x_4959_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_a_4957_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
}
}
else
{
lean_dec_ref(v_p_4920_);
lean_dec_ref(v_proof_4918_);
return v___x_4943_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4965_ = _args[0];
lean_object* v_generation_4966_ = _args[1];
lean_object* v_p_4967_ = _args[2];
lean_object* v_lhs_4968_ = _args[3];
lean_object* v_rhs_4969_ = _args[4];
lean_object* v_isNeg_4970_ = _args[5];
lean_object* v_isHEq_4971_ = _args[6];
lean_object* v_a_4972_ = _args[7];
lean_object* v_a_4973_ = _args[8];
lean_object* v_a_4974_ = _args[9];
lean_object* v_a_4975_ = _args[10];
lean_object* v_a_4976_ = _args[11];
lean_object* v_a_4977_ = _args[12];
lean_object* v_a_4978_ = _args[13];
lean_object* v_a_4979_ = _args[14];
lean_object* v_a_4980_ = _args[15];
lean_object* v_a_4981_ = _args[16];
lean_object* v_a_4982_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4983_; uint8_t v_isHEq_boxed_4984_; lean_object* v_res_4985_; 
v_isNeg_boxed_4983_ = lean_unbox(v_isNeg_4970_);
v_isHEq_boxed_4984_ = lean_unbox(v_isHEq_4971_);
v_res_4985_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4965_, v_generation_4966_, v_p_4967_, v_lhs_4968_, v_rhs_4969_, v_isNeg_boxed_4983_, v_isHEq_boxed_4984_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec(v_a_4975_);
lean_dec_ref(v_a_4974_);
lean_dec(v_a_4973_);
lean_dec(v_a_4972_);
return v_res_4985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4989_, lean_object* v_generation_4990_, lean_object* v_p_4991_, uint8_t v_isNeg_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_){
_start:
{
lean_object* v___x_5004_; 
lean_inc_ref(v_p_4991_);
v___x_5004_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4991_, v_a_5000_);
if (lean_obj_tag(v___x_5004_) == 0)
{
lean_object* v_a_5005_; lean_object* v___x_5006_; uint8_t v___x_5007_; 
v_a_5005_ = lean_ctor_get(v___x_5004_, 0);
lean_inc(v_a_5005_);
lean_dec_ref(v___x_5004_);
v___x_5006_ = l_Lean_Expr_cleanupAnnotations(v_a_5005_);
v___x_5007_ = l_Lean_Expr_isApp(v___x_5006_);
if (v___x_5007_ == 0)
{
lean_object* v___x_5008_; 
lean_dec_ref(v___x_5006_);
v___x_5008_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4989_, v_generation_4990_, v_p_4991_, v_isNeg_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
return v___x_5008_;
}
else
{
lean_object* v_arg_5009_; lean_object* v___x_5010_; uint8_t v___x_5011_; 
v_arg_5009_ = lean_ctor_get(v___x_5006_, 1);
lean_inc_ref(v_arg_5009_);
v___x_5010_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5006_);
v___x_5011_ = l_Lean_Expr_isApp(v___x_5010_);
if (v___x_5011_ == 0)
{
lean_object* v___x_5012_; 
lean_dec_ref(v___x_5010_);
lean_dec_ref(v_arg_5009_);
v___x_5012_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4989_, v_generation_4990_, v_p_4991_, v_isNeg_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
return v___x_5012_;
}
else
{
lean_object* v_arg_5013_; lean_object* v___x_5014_; uint8_t v___x_5015_; 
v_arg_5013_ = lean_ctor_get(v___x_5010_, 1);
lean_inc_ref(v_arg_5013_);
v___x_5014_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5010_);
v___x_5015_ = l_Lean_Expr_isApp(v___x_5014_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; 
lean_dec_ref(v___x_5014_);
lean_dec_ref(v_arg_5013_);
lean_dec_ref(v_arg_5009_);
v___x_5016_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4989_, v_generation_4990_, v_p_4991_, v_isNeg_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
return v___x_5016_;
}
else
{
lean_object* v_arg_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; uint8_t v___x_5020_; 
v_arg_5017_ = lean_ctor_get(v___x_5014_, 1);
lean_inc_ref(v_arg_5017_);
v___x_5018_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5014_);
v___x_5019_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5020_ = l_Lean_Expr_isConstOf(v___x_5018_, v___x_5019_);
if (v___x_5020_ == 0)
{
uint8_t v___x_5021_; 
lean_dec_ref(v_arg_5013_);
v___x_5021_ = l_Lean_Expr_isApp(v___x_5018_);
if (v___x_5021_ == 0)
{
lean_object* v___x_5022_; 
lean_dec_ref(v___x_5018_);
lean_dec_ref(v_arg_5017_);
lean_dec_ref(v_arg_5009_);
v___x_5022_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4989_, v_generation_4990_, v_p_4991_, v_isNeg_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
return v___x_5022_;
}
else
{
lean_object* v___x_5023_; lean_object* v___x_5024_; uint8_t v___x_5025_; 
v___x_5023_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5018_);
v___x_5024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5025_ = l_Lean_Expr_isConstOf(v___x_5023_, v___x_5024_);
lean_dec_ref(v___x_5023_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; 
lean_dec_ref(v_arg_5017_);
lean_dec_ref(v_arg_5009_);
v___x_5026_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4989_, v_generation_4990_, v_p_4991_, v_isNeg_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
return v___x_5026_;
}
else
{
lean_object* v___x_5027_; 
v___x_5027_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4989_, v_generation_4990_, v_p_4991_, v_arg_5017_, v_arg_5009_, v_isNeg_4992_, v___x_5025_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
return v___x_5027_;
}
}
}
else
{
uint8_t v___x_5028_; 
lean_dec_ref(v___x_5018_);
v___x_5028_ = l_Lean_Expr_isProp(v_arg_5017_);
lean_dec_ref(v_arg_5017_);
if (v___x_5028_ == 0)
{
lean_object* v___x_5029_; 
v___x_5029_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4989_, v_generation_4990_, v_p_4991_, v_arg_5013_, v_arg_5009_, v_isNeg_4992_, v___x_5028_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
return v___x_5029_;
}
else
{
lean_object* v___x_5030_; 
lean_dec_ref(v_arg_5013_);
lean_dec_ref(v_arg_5009_);
v___x_5030_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4989_, v_generation_4990_, v_p_4991_, v_isNeg_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
return v___x_5030_;
}
}
}
}
}
}
else
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5038_; 
lean_dec_ref(v_p_4991_);
lean_dec(v_generation_4990_);
lean_dec_ref(v_proof_4989_);
v_a_5031_ = lean_ctor_get(v___x_5004_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5004_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5033_ = v___x_5004_;
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v___x_5004_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5039_, lean_object* v_generation_5040_, lean_object* v_p_5041_, lean_object* v_isNeg_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_){
_start:
{
uint8_t v_isNeg_boxed_5054_; lean_object* v_res_5055_; 
v_isNeg_boxed_5054_ = lean_unbox(v_isNeg_5042_);
v_res_5055_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5039_, v_generation_5040_, v_p_5041_, v_isNeg_boxed_5054_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_, v_a_5051_, v_a_5052_);
lean_dec(v_a_5052_);
lean_dec_ref(v_a_5051_);
lean_dec(v_a_5050_);
lean_dec_ref(v_a_5049_);
lean_dec(v_a_5048_);
lean_dec_ref(v_a_5047_);
lean_dec(v_a_5046_);
lean_dec_ref(v_a_5045_);
lean_dec(v_a_5044_);
lean_dec(v_a_5043_);
return v_res_5055_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5064_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5065_ = l_Lean_Name_append(v___x_5064_, v___x_5063_);
return v___x_5065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5066_, lean_object* v_proof_5067_, lean_object* v_generation_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_){
_start:
{
lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v___y_5090_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v___y_5096_; lean_object* v___y_5097_; lean_object* v___y_5098_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___y_5103_; lean_object* v___x_5111_; lean_object* v_options_5112_; uint8_t v_hasTrace_5113_; 
lean_inc_ref(v_fact_5066_);
v___x_5111_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5066_, v_a_5069_);
lean_dec_ref(v___x_5111_);
v_options_5112_ = lean_ctor_get(v_a_5077_, 2);
v_hasTrace_5113_ = lean_ctor_get_uint8(v_options_5112_, sizeof(void*)*1);
if (v_hasTrace_5113_ == 0)
{
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
v___y_5096_ = v_a_5071_;
v___y_5097_ = v_a_5072_;
v___y_5098_ = v_a_5073_;
v___y_5099_ = v_a_5074_;
v___y_5100_ = v_a_5075_;
v___y_5101_ = v_a_5076_;
v___y_5102_ = v_a_5077_;
v___y_5103_ = v_a_5078_;
goto v___jp_5093_;
}
else
{
lean_object* v_inheritedTraceOptions_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; uint8_t v___x_5117_; 
v_inheritedTraceOptions_5114_ = lean_ctor_get(v_a_5077_, 13);
v___x_5115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5117_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5114_, v_options_5112_, v___x_5116_);
if (v___x_5117_ == 0)
{
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
v___y_5096_ = v_a_5071_;
v___y_5097_ = v_a_5072_;
v___y_5098_ = v_a_5073_;
v___y_5099_ = v_a_5074_;
v___y_5100_ = v_a_5075_;
v___y_5101_ = v_a_5076_;
v___y_5102_ = v_a_5077_;
v___y_5103_ = v_a_5078_;
goto v___jp_5093_;
}
else
{
lean_object* v___x_5118_; 
v___x_5118_ = l_Lean_Meta_Grind_updateLastTag(v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_);
if (lean_obj_tag(v___x_5118_) == 0)
{
lean_object* v___x_5119_; lean_object* v___x_5120_; 
lean_dec_ref(v___x_5118_);
lean_inc_ref(v_fact_5066_);
v___x_5119_ = l_Lean_MessageData_ofExpr(v_fact_5066_);
v___x_5120_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5115_, v___x_5119_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_dec_ref(v___x_5120_);
v___y_5094_ = v_a_5069_;
v___y_5095_ = v_a_5070_;
v___y_5096_ = v_a_5071_;
v___y_5097_ = v_a_5072_;
v___y_5098_ = v_a_5073_;
v___y_5099_ = v_a_5074_;
v___y_5100_ = v_a_5075_;
v___y_5101_ = v_a_5076_;
v___y_5102_ = v_a_5077_;
v___y_5103_ = v_a_5078_;
goto v___jp_5093_;
}
else
{
lean_dec(v_generation_5068_);
lean_dec_ref(v_proof_5067_);
lean_dec_ref(v_fact_5066_);
return v___x_5120_;
}
}
else
{
lean_dec(v_generation_5068_);
lean_dec_ref(v_proof_5067_);
lean_dec_ref(v_fact_5066_);
return v___x_5118_;
}
}
}
v___jp_5080_:
{
uint8_t v___x_5091_; lean_object* v___x_5092_; 
v___x_5091_ = 0;
v___x_5092_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5067_, v_generation_5068_, v_fact_5066_, v___x_5091_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_);
return v___x_5092_;
}
v___jp_5093_:
{
lean_object* v___x_5104_; uint8_t v___x_5105_; 
lean_inc_ref(v_fact_5066_);
v___x_5104_ = l_Lean_Expr_cleanupAnnotations(v_fact_5066_);
v___x_5105_ = l_Lean_Expr_isApp(v___x_5104_);
if (v___x_5105_ == 0)
{
lean_dec_ref(v___x_5104_);
v___y_5081_ = v___y_5094_;
v___y_5082_ = v___y_5095_;
v___y_5083_ = v___y_5096_;
v___y_5084_ = v___y_5097_;
v___y_5085_ = v___y_5098_;
v___y_5086_ = v___y_5099_;
v___y_5087_ = v___y_5100_;
v___y_5088_ = v___y_5101_;
v___y_5089_ = v___y_5102_;
v___y_5090_ = v___y_5103_;
goto v___jp_5080_;
}
else
{
lean_object* v_arg_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; uint8_t v___x_5109_; 
v_arg_5106_ = lean_ctor_get(v___x_5104_, 1);
lean_inc_ref(v_arg_5106_);
v___x_5107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5104_);
v___x_5108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5109_ = l_Lean_Expr_isConstOf(v___x_5107_, v___x_5108_);
lean_dec_ref(v___x_5107_);
if (v___x_5109_ == 0)
{
lean_dec_ref(v_arg_5106_);
v___y_5081_ = v___y_5094_;
v___y_5082_ = v___y_5095_;
v___y_5083_ = v___y_5096_;
v___y_5084_ = v___y_5097_;
v___y_5085_ = v___y_5098_;
v___y_5086_ = v___y_5099_;
v___y_5087_ = v___y_5100_;
v___y_5088_ = v___y_5101_;
v___y_5089_ = v___y_5102_;
v___y_5090_ = v___y_5103_;
goto v___jp_5080_;
}
else
{
lean_object* v___x_5110_; 
lean_dec_ref(v_fact_5066_);
v___x_5110_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5067_, v_generation_5068_, v_arg_5106_, v___x_5109_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_);
return v___x_5110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5121_, lean_object* v_proof_5122_, lean_object* v_generation_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_){
_start:
{
lean_object* v_res_5135_; 
v_res_5135_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5121_, v_proof_5122_, v_generation_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_);
lean_dec(v_a_5133_);
lean_dec_ref(v_a_5132_);
lean_dec(v_a_5131_);
lean_dec_ref(v_a_5130_);
lean_dec(v_a_5129_);
lean_dec_ref(v_a_5128_);
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_a_5125_);
lean_dec(v_a_5124_);
return v_res_5135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_){
_start:
{
lean_object* v___x_5150_; 
v___x_5150_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5139_);
if (lean_obj_tag(v___x_5150_) == 0)
{
lean_object* v_a_5151_; uint8_t v___x_5152_; 
v_a_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_a_5151_);
lean_dec_ref(v___x_5150_);
v___x_5152_ = lean_unbox(v_a_5151_);
lean_dec(v_a_5151_);
if (v___x_5152_ == 0)
{
lean_object* v___x_5153_; lean_object* v___x_5154_; 
v___x_5153_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5154_ = l_Lean_Core_checkSystem(v___x_5153_, v___y_5147_, v___y_5148_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v___x_5155_; 
lean_dec_ref(v___x_5154_);
v___x_5155_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5139_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5192_; 
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5158_ = v___x_5155_;
v_isShared_5159_ = v_isSharedCheck_5192_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5155_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5192_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
if (lean_obj_tag(v_a_5156_) == 1)
{
lean_object* v_val_5160_; 
lean_del_object(v___x_5158_);
v_val_5160_ = lean_ctor_get(v_a_5156_, 0);
lean_inc(v_val_5160_);
lean_dec_ref(v_a_5156_);
if (lean_obj_tag(v_val_5160_) == 0)
{
lean_object* v_lhs_5161_; lean_object* v_rhs_5162_; lean_object* v_proof_5163_; uint8_t v_isHEq_5164_; lean_object* v___x_5165_; 
v_lhs_5161_ = lean_ctor_get(v_val_5160_, 0);
lean_inc_ref(v_lhs_5161_);
v_rhs_5162_ = lean_ctor_get(v_val_5160_, 1);
lean_inc_ref(v_rhs_5162_);
v_proof_5163_ = lean_ctor_get(v_val_5160_, 2);
lean_inc_ref(v_proof_5163_);
v_isHEq_5164_ = lean_ctor_get_uint8(v_val_5160_, sizeof(void*)*3);
lean_dec_ref(v_val_5160_);
v___x_5165_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5161_, v_rhs_5162_, v_proof_5163_, v_isHEq_5164_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_dec_ref(v___x_5165_);
goto _start;
}
else
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5174_; 
v_a_5167_ = lean_ctor_get(v___x_5165_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5165_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5169_ = v___x_5165_;
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___x_5165_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5172_; 
if (v_isShared_5170_ == 0)
{
v___x_5172_ = v___x_5169_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5167_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
}
}
else
{
lean_object* v_prop_5175_; lean_object* v_proof_5176_; lean_object* v_generation_5177_; lean_object* v___x_5178_; 
v_prop_5175_ = lean_ctor_get(v_val_5160_, 0);
lean_inc_ref(v_prop_5175_);
v_proof_5176_ = lean_ctor_get(v_val_5160_, 1);
lean_inc_ref(v_proof_5176_);
v_generation_5177_ = lean_ctor_get(v_val_5160_, 2);
lean_inc(v_generation_5177_);
lean_dec_ref(v_val_5160_);
v___x_5178_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5175_, v_proof_5176_, v_generation_5177_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
if (lean_obj_tag(v___x_5178_) == 0)
{
lean_dec_ref(v___x_5178_);
goto _start;
}
else
{
lean_object* v_a_5180_; lean_object* v___x_5182_; uint8_t v_isShared_5183_; uint8_t v_isSharedCheck_5187_; 
v_a_5180_ = lean_ctor_get(v___x_5178_, 0);
v_isSharedCheck_5187_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5187_ == 0)
{
v___x_5182_ = v___x_5178_;
v_isShared_5183_ = v_isSharedCheck_5187_;
goto v_resetjp_5181_;
}
else
{
lean_inc(v_a_5180_);
lean_dec(v___x_5178_);
v___x_5182_ = lean_box(0);
v_isShared_5183_ = v_isSharedCheck_5187_;
goto v_resetjp_5181_;
}
v_resetjp_5181_:
{
lean_object* v___x_5185_; 
if (v_isShared_5183_ == 0)
{
v___x_5185_ = v___x_5182_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5186_; 
v_reuseFailAlloc_5186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5186_, 0, v_a_5180_);
v___x_5185_ = v_reuseFailAlloc_5186_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
return v___x_5185_;
}
}
}
}
}
else
{
lean_object* v___x_5188_; lean_object* v___x_5190_; 
lean_dec(v_a_5156_);
v___x_5188_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5159_ == 0)
{
lean_ctor_set(v___x_5158_, 0, v___x_5188_);
v___x_5190_ = v___x_5158_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5188_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
v_a_5193_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5155_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5155_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
else
{
lean_object* v_a_5201_; lean_object* v___x_5203_; uint8_t v_isShared_5204_; uint8_t v_isSharedCheck_5208_; 
v_a_5201_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5208_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5203_ = v___x_5154_;
v_isShared_5204_ = v_isSharedCheck_5208_;
goto v_resetjp_5202_;
}
else
{
lean_inc(v_a_5201_);
lean_dec(v___x_5154_);
v___x_5203_ = lean_box(0);
v_isShared_5204_ = v_isSharedCheck_5208_;
goto v_resetjp_5202_;
}
v_resetjp_5202_:
{
lean_object* v___x_5206_; 
if (v_isShared_5204_ == 0)
{
v___x_5206_ = v___x_5203_;
goto v_reusejp_5205_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v_a_5201_);
v___x_5206_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5205_;
}
v_reusejp_5205_:
{
return v___x_5206_;
}
}
}
}
else
{
lean_object* v___x_5209_; 
v___x_5209_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5139_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5217_; 
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5217_ == 0)
{
lean_object* v_unused_5218_; 
v_unused_5218_ = lean_ctor_get(v___x_5209_, 0);
lean_dec(v_unused_5218_);
v___x_5211_ = v___x_5209_;
v_isShared_5212_ = v_isSharedCheck_5217_;
goto v_resetjp_5210_;
}
else
{
lean_dec(v___x_5209_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5217_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5213_; lean_object* v___x_5215_; 
v___x_5213_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5212_ == 0)
{
lean_ctor_set(v___x_5211_, 0, v___x_5213_);
v___x_5215_ = v___x_5211_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v___x_5213_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
else
{
lean_object* v_a_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5226_; 
v_a_5219_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5226_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5221_ = v___x_5209_;
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_a_5219_);
lean_dec(v___x_5209_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
lean_object* v___x_5224_; 
if (v_isShared_5222_ == 0)
{
v___x_5224_ = v___x_5221_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_a_5219_);
v___x_5224_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
return v___x_5224_;
}
}
}
}
}
else
{
lean_object* v_a_5227_; lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5234_; 
v_a_5227_ = lean_ctor_get(v___x_5150_, 0);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5150_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5229_ = v___x_5150_;
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_a_5227_);
lean_dec(v___x_5150_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5234_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v___x_5232_; 
if (v_isShared_5230_ == 0)
{
v___x_5232_ = v___x_5229_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5233_; 
v_reuseFailAlloc_5233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_a_5227_);
v___x_5232_ = v_reuseFailAlloc_5233_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
return v___x_5232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
lean_dec(v___y_5236_);
lean_dec(v___y_5235_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_){
_start:
{
lean_object* v___x_5258_; 
v___x_5258_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_);
lean_dec(v_a_5256_);
lean_dec_ref(v_a_5255_);
lean_dec(v_a_5254_);
lean_dec_ref(v_a_5253_);
lean_dec(v_a_5252_);
lean_dec_ref(v_a_5251_);
lean_dec(v_a_5250_);
lean_dec_ref(v_a_5249_);
lean_dec(v_a_5248_);
lean_dec(v_a_5247_);
if (lean_obj_tag(v___x_5258_) == 0)
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5272_; 
v_a_5259_ = lean_ctor_get(v___x_5258_, 0);
v_isSharedCheck_5272_ = !lean_is_exclusive(v___x_5258_);
if (v_isSharedCheck_5272_ == 0)
{
v___x_5261_ = v___x_5258_;
v_isShared_5262_ = v_isSharedCheck_5272_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5258_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5272_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v_fst_5263_; 
v_fst_5263_ = lean_ctor_get(v_a_5259_, 0);
lean_inc(v_fst_5263_);
lean_dec(v_a_5259_);
if (lean_obj_tag(v_fst_5263_) == 0)
{
lean_object* v___x_5264_; lean_object* v___x_5266_; 
v___x_5264_ = lean_box(0);
if (v_isShared_5262_ == 0)
{
lean_ctor_set(v___x_5261_, 0, v___x_5264_);
v___x_5266_ = v___x_5261_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5267_; 
v_reuseFailAlloc_5267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5267_, 0, v___x_5264_);
v___x_5266_ = v_reuseFailAlloc_5267_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
return v___x_5266_;
}
}
else
{
lean_object* v_val_5268_; lean_object* v___x_5270_; 
v_val_5268_ = lean_ctor_get(v_fst_5263_, 0);
lean_inc(v_val_5268_);
lean_dec_ref(v_fst_5263_);
if (v_isShared_5262_ == 0)
{
lean_ctor_set(v___x_5261_, 0, v_val_5268_);
v___x_5270_ = v___x_5261_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_val_5268_);
v___x_5270_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
return v___x_5270_;
}
}
}
}
else
{
lean_object* v_a_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5280_; 
v_a_5273_ = lean_ctor_get(v___x_5258_, 0);
v_isSharedCheck_5280_ = !lean_is_exclusive(v___x_5258_);
if (v_isSharedCheck_5280_ == 0)
{
v___x_5275_ = v___x_5258_;
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_a_5273_);
lean_dec(v___x_5258_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5278_; 
if (v_isShared_5276_ == 0)
{
v___x_5278_ = v___x_5275_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v_a_5273_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_){
_start:
{
lean_object* v_res_5292_; 
v_res_5292_ = lean_grind_process_new_facts(v_a_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_);
return v_res_5292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_inst_5293_, lean_object* v_a_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_){
_start:
{
lean_object* v___x_5306_; 
v___x_5306_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
return v___x_5306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_inst_5307_, lean_object* v_a_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_inst_5307_, v_a_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec(v___y_5316_);
lean_dec_ref(v___y_5315_);
lean_dec(v___y_5314_);
lean_dec_ref(v___y_5313_);
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
lean_dec(v___y_5310_);
lean_dec(v___y_5309_);
lean_dec_ref(v_a_5308_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5321_, lean_object* v_proof_5322_, lean_object* v_generation_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_){
_start:
{
uint8_t v___x_5335_; 
lean_inc_ref(v_fact_5321_);
v___x_5335_ = l_Lean_Expr_isTrue(v_fact_5321_);
if (v___x_5335_ == 0)
{
lean_object* v___x_5336_; 
v___x_5336_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5324_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_object* v_a_5337_; lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5348_; 
v_a_5337_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5339_ = v___x_5336_;
v_isShared_5340_ = v_isSharedCheck_5348_;
goto v_resetjp_5338_;
}
else
{
lean_inc(v_a_5337_);
lean_dec(v___x_5336_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5348_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
uint8_t v___x_5341_; 
v___x_5341_ = lean_unbox(v_a_5337_);
lean_dec(v_a_5337_);
if (v___x_5341_ == 0)
{
lean_object* v___x_5342_; lean_object* v___x_5343_; 
lean_del_object(v___x_5339_);
v___x_5342_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5324_);
lean_dec_ref(v___x_5342_);
v___x_5343_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5321_, v_proof_5322_, v_generation_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_);
return v___x_5343_;
}
else
{
lean_object* v___x_5344_; lean_object* v___x_5346_; 
lean_dec(v_generation_5323_);
lean_dec_ref(v_proof_5322_);
lean_dec_ref(v_fact_5321_);
v___x_5344_ = lean_box(0);
if (v_isShared_5340_ == 0)
{
lean_ctor_set(v___x_5339_, 0, v___x_5344_);
v___x_5346_ = v___x_5339_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v___x_5344_);
v___x_5346_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
return v___x_5346_;
}
}
}
}
else
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5356_; 
lean_dec(v_generation_5323_);
lean_dec_ref(v_proof_5322_);
lean_dec_ref(v_fact_5321_);
v_a_5349_ = lean_ctor_get(v___x_5336_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5351_ = v___x_5336_;
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5336_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5354_; 
if (v_isShared_5352_ == 0)
{
v___x_5354_ = v___x_5351_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
}
else
{
lean_object* v___x_5357_; lean_object* v___x_5358_; 
lean_dec(v_generation_5323_);
lean_dec_ref(v_proof_5322_);
lean_dec_ref(v_fact_5321_);
v___x_5357_ = lean_box(0);
v___x_5358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5358_, 0, v___x_5357_);
return v___x_5358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5359_, lean_object* v_proof_5360_, lean_object* v_generation_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l_Lean_Meta_Grind_add(v_fact_5359_, v_proof_5360_, v_generation_5361_, v_a_5362_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_, v_a_5370_, v_a_5371_);
lean_dec(v_a_5371_);
lean_dec_ref(v_a_5370_);
lean_dec(v_a_5369_);
lean_dec_ref(v_a_5368_);
lean_dec(v_a_5367_);
lean_dec_ref(v_a_5366_);
lean_dec(v_a_5365_);
lean_dec_ref(v_a_5364_);
lean_dec(v_a_5363_);
lean_dec(v_a_5362_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5374_, lean_object* v_generation_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_){
_start:
{
lean_object* v___x_5387_; 
lean_inc(v_fvarId_5374_);
v___x_5387_ = l_Lean_FVarId_getType___redArg(v_fvarId_5374_, v_a_5382_, v_a_5384_, v_a_5385_);
if (lean_obj_tag(v___x_5387_) == 0)
{
lean_object* v_a_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; 
v_a_5388_ = lean_ctor_get(v___x_5387_, 0);
lean_inc(v_a_5388_);
lean_dec_ref(v___x_5387_);
v___x_5389_ = l_Lean_mkFVar(v_fvarId_5374_);
v___x_5390_ = l_Lean_Meta_Grind_add(v_a_5388_, v___x_5389_, v_generation_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_, v_a_5382_, v_a_5383_, v_a_5384_, v_a_5385_);
return v___x_5390_;
}
else
{
lean_object* v_a_5391_; lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5398_; 
lean_dec(v_generation_5375_);
lean_dec(v_fvarId_5374_);
v_a_5391_ = lean_ctor_get(v___x_5387_, 0);
v_isSharedCheck_5398_ = !lean_is_exclusive(v___x_5387_);
if (v_isSharedCheck_5398_ == 0)
{
v___x_5393_ = v___x_5387_;
v_isShared_5394_ = v_isSharedCheck_5398_;
goto v_resetjp_5392_;
}
else
{
lean_inc(v_a_5391_);
lean_dec(v___x_5387_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5399_, lean_object* v_generation_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_){
_start:
{
lean_object* v_res_5412_; 
v_res_5412_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5399_, v_generation_5400_, v_a_5401_, v_a_5402_, v_a_5403_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_, v_a_5410_);
lean_dec(v_a_5410_);
lean_dec_ref(v_a_5409_);
lean_dec(v_a_5408_);
lean_dec_ref(v_a_5407_);
lean_dec(v_a_5406_);
lean_dec_ref(v_a_5405_);
lean_dec(v_a_5404_);
lean_dec_ref(v_a_5403_);
lean_dec(v_a_5402_);
lean_dec(v_a_5401_);
return v_res_5412_;
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
