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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_246_);
v___x_252_ = lean_box(0);
return v___x_252_;
}
else
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_array_fget_borrowed(v_xs_247_, v_i_249_);
lean_inc_ref(v_v_248_);
lean_inc(v___x_253_);
lean_inc_ref(v___x_246_);
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
lean_dec_ref(v___x_246_);
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
lean_dec_ref(v___x_279_);
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
size_t v_x_28160__boxed_356_; lean_object* v_res_357_; 
v_x_28160__boxed_356_ = lean_unbox_usize(v_x_354_);
lean_dec(v_x_354_);
v_res_357_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_352_, v_x_353_, v_x_28160__boxed_356_, v_x_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
uint64_t v___x_361_; size_t v_h_362_; lean_object* v___x_363_; 
lean_inc_ref(v_x_360_);
lean_inc_ref(v___x_358_);
v___x_361_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_358_, v_x_360_);
v_h_362_ = lean_uint64_to_usize(v___x_361_);
v___x_363_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_358_, v_x_359_, v_h_362_, v_x_360_);
return v___x_363_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_375_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_376_ = l_Lean_Name_append(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7));
v___x_379_ = l_Lean_stringToMessageData(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object* v_as_x27_380_, lean_object* v_b_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
if (lean_obj_tag(v_as_x27_380_) == 0)
{
lean_object* v___x_393_; 
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v_b_381_);
return v___x_393_;
}
else
{
lean_object* v_head_394_; lean_object* v_tail_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_468_; 
v_head_394_ = lean_ctor_get(v_as_x27_380_, 0);
v_tail_395_ = lean_ctor_get(v_as_x27_380_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v_as_x27_380_);
if (v_isSharedCheck_468_ == 0)
{
v___x_397_ = v_as_x27_380_;
v_isShared_398_ = v_isSharedCheck_468_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_tail_395_);
lean_inc(v_head_394_);
lean_dec(v_as_x27_380_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_468_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___y_401_; uint8_t v_a_441_; uint8_t v___x_456_; 
v___x_399_ = lean_box(0);
v___x_456_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_394_);
if (v___x_456_ == 0)
{
v_a_441_ = v___x_456_;
goto v___jp_440_;
}
else
{
lean_object* v___x_457_; 
lean_inc(v_head_394_);
v___x_457_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_394_, v___y_382_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; uint8_t v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref(v___x_457_);
v___x_459_ = lean_unbox(v_a_458_);
lean_dec(v_a_458_);
v_a_441_ = v___x_459_;
goto v___jp_440_;
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_del_object(v___x_397_);
lean_dec(v_tail_395_);
lean_dec(v_head_394_);
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
v___jp_400_:
{
lean_object* v___x_402_; lean_object* v_toGoalState_403_; lean_object* v_mvarId_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_439_; 
v___x_402_ = lean_st_ref_take(v___y_401_);
v_toGoalState_403_ = lean_ctor_get(v___x_402_, 0);
v_mvarId_404_ = lean_ctor_get(v___x_402_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_439_ == 0)
{
v___x_406_ = v___x_402_;
v_isShared_407_ = v_isSharedCheck_439_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_mvarId_404_);
lean_inc(v_toGoalState_403_);
lean_dec(v___x_402_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_439_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_nextDeclIdx_408_; lean_object* v_enodeMap_409_; lean_object* v_exprs_410_; lean_object* v_parents_411_; lean_object* v_congrTable_412_; lean_object* v_appMap_413_; lean_object* v_indicesFound_414_; lean_object* v_newFacts_415_; uint8_t v_inconsistent_416_; lean_object* v_nextIdx_417_; lean_object* v_newRawFacts_418_; lean_object* v_facts_419_; lean_object* v_extThms_420_; lean_object* v_ematch_421_; lean_object* v_inj_422_; lean_object* v_split_423_; lean_object* v_clean_424_; lean_object* v_sstates_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_438_; 
v_nextDeclIdx_408_ = lean_ctor_get(v_toGoalState_403_, 0);
v_enodeMap_409_ = lean_ctor_get(v_toGoalState_403_, 1);
v_exprs_410_ = lean_ctor_get(v_toGoalState_403_, 2);
v_parents_411_ = lean_ctor_get(v_toGoalState_403_, 3);
v_congrTable_412_ = lean_ctor_get(v_toGoalState_403_, 4);
v_appMap_413_ = lean_ctor_get(v_toGoalState_403_, 5);
v_indicesFound_414_ = lean_ctor_get(v_toGoalState_403_, 6);
v_newFacts_415_ = lean_ctor_get(v_toGoalState_403_, 7);
v_inconsistent_416_ = lean_ctor_get_uint8(v_toGoalState_403_, sizeof(void*)*17);
v_nextIdx_417_ = lean_ctor_get(v_toGoalState_403_, 8);
v_newRawFacts_418_ = lean_ctor_get(v_toGoalState_403_, 9);
v_facts_419_ = lean_ctor_get(v_toGoalState_403_, 10);
v_extThms_420_ = lean_ctor_get(v_toGoalState_403_, 11);
v_ematch_421_ = lean_ctor_get(v_toGoalState_403_, 12);
v_inj_422_ = lean_ctor_get(v_toGoalState_403_, 13);
v_split_423_ = lean_ctor_get(v_toGoalState_403_, 14);
v_clean_424_ = lean_ctor_get(v_toGoalState_403_, 15);
v_sstates_425_ = lean_ctor_get(v_toGoalState_403_, 16);
v_isSharedCheck_438_ = !lean_is_exclusive(v_toGoalState_403_);
if (v_isSharedCheck_438_ == 0)
{
v___x_427_ = v_toGoalState_403_;
v_isShared_428_ = v_isSharedCheck_438_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_sstates_425_);
lean_inc(v_clean_424_);
lean_inc(v_split_423_);
lean_inc(v_inj_422_);
lean_inc(v_ematch_421_);
lean_inc(v_extThms_420_);
lean_inc(v_facts_419_);
lean_inc(v_newRawFacts_418_);
lean_inc(v_nextIdx_417_);
lean_inc(v_newFacts_415_);
lean_inc(v_indicesFound_414_);
lean_inc(v_appMap_413_);
lean_inc(v_congrTable_412_);
lean_inc(v_parents_411_);
lean_inc(v_exprs_410_);
lean_inc(v_enodeMap_409_);
lean_inc(v_nextDeclIdx_408_);
lean_dec(v_toGoalState_403_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_438_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_inc_ref(v_enodeMap_409_);
v___x_429_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_409_, v_congrTable_412_, v_head_394_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 4, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_nextDeclIdx_408_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_enodeMap_409_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_exprs_410_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_parents_411_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_437_, 5, v_appMap_413_);
lean_ctor_set(v_reuseFailAlloc_437_, 6, v_indicesFound_414_);
lean_ctor_set(v_reuseFailAlloc_437_, 7, v_newFacts_415_);
lean_ctor_set(v_reuseFailAlloc_437_, 8, v_nextIdx_417_);
lean_ctor_set(v_reuseFailAlloc_437_, 9, v_newRawFacts_418_);
lean_ctor_set(v_reuseFailAlloc_437_, 10, v_facts_419_);
lean_ctor_set(v_reuseFailAlloc_437_, 11, v_extThms_420_);
lean_ctor_set(v_reuseFailAlloc_437_, 12, v_ematch_421_);
lean_ctor_set(v_reuseFailAlloc_437_, 13, v_inj_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 14, v_split_423_);
lean_ctor_set(v_reuseFailAlloc_437_, 15, v_clean_424_);
lean_ctor_set(v_reuseFailAlloc_437_, 16, v_sstates_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*17, v_inconsistent_416_);
v___x_431_ = v_reuseFailAlloc_437_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_431_);
v___x_433_ = v___x_406_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_mvarId_404_);
v___x_433_ = v_reuseFailAlloc_436_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; 
v___x_434_ = lean_st_ref_set(v___y_401_, v___x_433_);
v_as_x27_380_ = v_tail_395_;
v_b_381_ = v___x_399_;
goto _start;
}
}
}
}
}
v___jp_440_:
{
if (v_a_441_ == 0)
{
lean_del_object(v___x_397_);
lean_dec(v_head_394_);
v_as_x27_380_ = v_tail_395_;
v_b_381_ = v___x_399_;
goto _start;
}
else
{
lean_object* v_options_443_; uint8_t v_hasTrace_444_; 
v_options_443_ = lean_ctor_get(v___y_390_, 2);
v_hasTrace_444_ = lean_ctor_get_uint8(v_options_443_, sizeof(void*)*1);
if (v_hasTrace_444_ == 0)
{
lean_del_object(v___x_397_);
v___y_401_ = v___y_382_;
goto v___jp_400_;
}
else
{
lean_object* v_inheritedTraceOptions_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_inheritedTraceOptions_445_ = lean_ctor_get(v___y_390_, 13);
v___x_446_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_447_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_448_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_445_, v_options_443_, v___x_447_);
if (v___x_448_ == 0)
{
lean_del_object(v___x_397_);
v___y_401_ = v___y_382_;
goto v___jp_400_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Grind_updateLastTag(v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
lean_dec_ref(v___x_449_);
v___x_450_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_394_);
v___x_451_ = l_Lean_MessageData_ofExpr(v_head_394_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 7);
lean_ctor_set(v___x_397_, 1, v___x_451_);
lean_ctor_set(v___x_397_, 0, v___x_450_);
v___x_453_ = v___x_397_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_451_);
v___x_453_ = v_reuseFailAlloc_455_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_446_, v___x_453_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_dec_ref(v___x_454_);
v___y_401_ = v___y_382_;
goto v___jp_400_;
}
else
{
lean_dec(v_tail_395_);
lean_dec(v_head_394_);
return v___x_454_;
}
}
}
else
{
lean_del_object(v___x_397_);
lean_dec(v_tail_395_);
lean_dec(v_head_394_);
return v___x_449_;
}
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_534_, lean_object* v_msg_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_534_, v_msg_535_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_548_, lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_548_, v_msg_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec(v___y_550_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_562_, lean_object* v_as_x27_563_, lean_object* v_b_564_, lean_object* v_a_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_563_, v_b_564_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_578_, lean_object* v_as_x27_579_, lean_object* v_b_580_, lean_object* v_a_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_578_, v_as_x27_579_, v_b_580_, v_a_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec(v___y_582_);
lean_dec(v_as_578_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_594_, lean_object* v_00_u03b2_595_, lean_object* v_x_596_, size_t v_x_597_, lean_object* v_x_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_594_, v_x_596_, v_x_597_, v_x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_600_, lean_object* v_00_u03b2_601_, lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
size_t v_x_28634__boxed_605_; lean_object* v_res_606_; 
v_x_28634__boxed_605_ = lean_unbox_usize(v_x_603_);
lean_dec(v_x_603_);
v_res_606_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_600_, v_00_u03b2_601_, v_x_602_, v_x_28634__boxed_605_, v_x_604_);
return v_res_606_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_609_ = l_Lean_stringToMessageData(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_610_, lean_object* v_b_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
if (lean_obj_tag(v_as_x27_610_) == 0)
{
lean_object* v___x_623_; 
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v_b_611_);
return v___x_623_;
}
else
{
lean_object* v_head_624_; lean_object* v_tail_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_671_; 
v_head_624_ = lean_ctor_get(v_as_x27_610_, 0);
v_tail_625_ = lean_ctor_get(v_as_x27_610_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_as_x27_610_);
if (v_isSharedCheck_671_ == 0)
{
v___x_627_ = v_as_x27_610_;
v_isShared_628_ = v_isSharedCheck_671_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_tail_625_);
lean_inc(v_head_624_);
lean_dec(v_as_x27_610_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_671_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; uint8_t v_a_644_; uint8_t v___x_659_; 
v___x_629_ = lean_box(0);
v___x_659_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_624_);
if (v___x_659_ == 0)
{
v_a_644_ = v___x_659_;
goto v___jp_643_;
}
else
{
lean_object* v___x_660_; 
lean_inc(v_head_624_);
v___x_660_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_624_, v___y_612_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; uint8_t v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref(v___x_660_);
v___x_662_ = lean_unbox(v_a_661_);
lean_dec(v_a_661_);
v_a_644_ = v___x_662_;
goto v___jp_643_;
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_del_object(v___x_627_);
lean_dec(v_tail_625_);
lean_dec(v_head_624_);
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
v___jp_630_:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Meta_Grind_addCongrTable(v_head_624_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_dec_ref(v___x_641_);
v_as_x27_610_ = v_tail_625_;
v_b_611_ = v___x_629_;
goto _start;
}
else
{
lean_dec(v_tail_625_);
return v___x_641_;
}
}
v___jp_643_:
{
if (v_a_644_ == 0)
{
lean_del_object(v___x_627_);
lean_dec(v_head_624_);
v_as_x27_610_ = v_tail_625_;
v_b_611_ = v___x_629_;
goto _start;
}
else
{
lean_object* v_options_646_; uint8_t v_hasTrace_647_; 
v_options_646_ = lean_ctor_get(v___y_620_, 2);
v_hasTrace_647_ = lean_ctor_get_uint8(v_options_646_, sizeof(void*)*1);
if (v_hasTrace_647_ == 0)
{
lean_del_object(v___x_627_);
v___y_631_ = v___y_612_;
v___y_632_ = v___y_613_;
v___y_633_ = v___y_614_;
v___y_634_ = v___y_615_;
v___y_635_ = v___y_616_;
v___y_636_ = v___y_617_;
v___y_637_ = v___y_618_;
v___y_638_ = v___y_619_;
v___y_639_ = v___y_620_;
v___y_640_ = v___y_621_;
goto v___jp_630_;
}
else
{
lean_object* v_inheritedTraceOptions_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_inheritedTraceOptions_648_ = lean_ctor_get(v___y_620_, 13);
v___x_649_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_650_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_651_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_648_, v_options_646_, v___x_650_);
if (v___x_651_ == 0)
{
lean_del_object(v___x_627_);
v___y_631_ = v___y_612_;
v___y_632_ = v___y_613_;
v___y_633_ = v___y_614_;
v___y_634_ = v___y_615_;
v___y_635_ = v___y_616_;
v___y_636_ = v___y_617_;
v___y_637_ = v___y_618_;
v___y_638_ = v___y_619_;
v___y_639_ = v___y_620_;
v___y_640_ = v___y_621_;
goto v___jp_630_;
}
else
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Meta_Grind_updateLastTag(v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
lean_dec_ref(v___x_652_);
v___x_653_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_624_);
v___x_654_ = l_Lean_MessageData_ofExpr(v_head_624_);
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 7);
lean_ctor_set(v___x_627_, 1, v___x_654_);
lean_ctor_set(v___x_627_, 0, v___x_653_);
v___x_656_ = v___x_627_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_654_);
v___x_656_ = v_reuseFailAlloc_658_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_649_, v___x_656_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref(v___x_657_);
v___y_631_ = v___y_612_;
v___y_632_ = v___y_613_;
v___y_633_ = v___y_614_;
v___y_634_ = v___y_615_;
v___y_635_ = v___y_616_;
v___y_636_ = v___y_617_;
v___y_637_ = v___y_618_;
v___y_638_ = v___y_619_;
v___y_639_ = v___y_620_;
v___y_640_ = v___y_621_;
goto v___jp_630_;
}
else
{
lean_dec(v_tail_625_);
lean_dec(v_head_624_);
return v___x_657_;
}
}
}
else
{
lean_del_object(v___x_627_);
lean_dec(v_tail_625_);
lean_dec(v_head_624_);
return v___x_652_;
}
}
}
}
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
return v___x_760_;
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
lean_object* v_es_772_; lean_object* v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; lean_object* v_j_777_; lean_object* v___x_778_; 
v_es_772_ = lean_ctor_get(v_x_769_, 0);
v___x_773_ = lean_box(2);
v___x_774_ = ((size_t)5ULL);
v___x_775_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_776_ = lean_usize_land(v_x_770_, v___x_775_);
v_j_777_ = lean_usize_to_nat(v___x_776_);
v___x_778_ = lean_array_get_borrowed(v___x_773_, v_es_772_, v_j_777_);
lean_dec(v_j_777_);
switch(lean_obj_tag(v___x_778_))
{
case 0:
{
lean_object* v_key_779_; uint8_t v___x_780_; 
v_key_779_ = lean_ctor_get(v___x_778_, 0);
v___x_780_ = l_Lean_instBEqMVarId_beq(v_x_771_, v_key_779_);
return v___x_780_;
}
case 1:
{
lean_object* v_node_781_; size_t v___x_782_; 
v_node_781_ = lean_ctor_get(v___x_778_, 0);
v___x_782_ = lean_usize_shift_right(v_x_770_, v___x_774_);
v_x_769_ = v_node_781_;
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
size_t v_x_10241__boxed_791_; uint8_t v_res_792_; lean_object* v_r_793_; 
v_x_10241__boxed_791_ = lean_unbox_usize(v_x_789_);
lean_dec(v_x_789_);
v_res_792_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_788_, v_x_10241__boxed_791_, v_x_790_);
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
lean_dec_ref(v___x_854_);
v___x_856_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_855_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref(v___x_856_);
v___x_858_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_839_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_839_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref(v___x_860_);
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
size_t v_x_10526__boxed_959_; uint8_t v_res_960_; lean_object* v_r_961_; 
v_x_10526__boxed_959_ = lean_unbox_usize(v_x_957_);
lean_dec(v_x_957_);
v_res_960_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_955_, v_x_956_, v_x_10526__boxed_959_, v_x_958_);
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
lean_dec_ref(v___x_996_);
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
lean_dec_ref(v___x_998_);
lean_inc(v_a_997_);
v___x_1000_ = l_Lean_Meta_mkDecide(v_a_997_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref(v___x_1000_);
v___x_1002_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_989_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref(v___x_1002_);
v___x_1004_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_1005_ = l_Lean_Expr_appArg_x21(v_a_1001_);
lean_dec(v_a_1001_);
v___x_1006_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_997_);
v___x_1007_ = l_Lean_mkApp3(v___x_1004_, v_a_997_, v___x_1005_, v___x_1006_);
v___x_1008_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1009_ = l_Lean_mkApp4(v___x_1008_, v_a_997_, v_a_1003_, v___x_1007_, v_a_999_);
v___x_1010_ = l_Lean_Meta_Grind_closeGoal(v___x_1009_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
return v___x_1010_;
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_a_1001_);
lean_dec(v_a_999_);
lean_dec(v_a_997_);
v_a_1011_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1002_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1002_);
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
lean_object* v_head_1072_; lean_object* v_tail_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_head_1072_ = lean_ctor_get(v_as_x27_1058_, 0);
lean_inc_n(v_head_1072_, 2);
v_tail_1073_ = lean_ctor_get(v_as_x27_1058_, 1);
lean_inc(v_tail_1073_);
lean_dec_ref(v_as_x27_1058_);
v___x_1074_ = lean_st_ref_get(v___y_1060_);
v___x_1075_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1074_, v_head_1072_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v_self_1077_; lean_object* v_next_1078_; lean_object* v_root_1079_; lean_object* v_congr_1080_; lean_object* v_target_x3f_1081_; lean_object* v_proof_x3f_1082_; uint8_t v_flipped_1083_; lean_object* v_size_1084_; uint8_t v_interpreted_1085_; uint8_t v_ctor_1086_; uint8_t v_hasLambdas_1087_; uint8_t v_heqProofs_1088_; lean_object* v_idx_1089_; lean_object* v_generation_1090_; lean_object* v_mt_1091_; lean_object* v_sTerms_1092_; uint8_t v_funCC_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1106_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref(v___x_1075_);
v_self_1077_ = lean_ctor_get(v_a_1076_, 0);
v_next_1078_ = lean_ctor_get(v_a_1076_, 1);
v_root_1079_ = lean_ctor_get(v_a_1076_, 2);
v_congr_1080_ = lean_ctor_get(v_a_1076_, 3);
v_target_x3f_1081_ = lean_ctor_get(v_a_1076_, 4);
v_proof_x3f_1082_ = lean_ctor_get(v_a_1076_, 5);
v_flipped_1083_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*11);
v_size_1084_ = lean_ctor_get(v_a_1076_, 6);
v_interpreted_1085_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*11 + 1);
v_ctor_1086_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*11 + 2);
v_hasLambdas_1087_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*11 + 3);
v_heqProofs_1088_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*11 + 4);
v_idx_1089_ = lean_ctor_get(v_a_1076_, 7);
v_generation_1090_ = lean_ctor_get(v_a_1076_, 8);
v_mt_1091_ = lean_ctor_get(v_a_1076_, 9);
v_sTerms_1092_ = lean_ctor_get(v_a_1076_, 10);
v_funCC_1093_ = lean_ctor_get_uint8(v_a_1076_, sizeof(void*)*11 + 5);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_a_1076_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1095_ = v_a_1076_;
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
else
{
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
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_nat_dec_lt(v_mt_1091_, v___x_1057_);
lean_dec(v_mt_1091_);
if (v___x_1098_ == 0)
{
lean_del_object(v___x_1095_);
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
lean_dec(v_head_1072_);
v_as_x27_1058_ = v_tail_1073_;
v_b_1059_ = v___x_1097_;
goto _start;
}
else
{
lean_object* v___x_1101_; 
lean_inc(v___x_1057_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 9, v___x_1057_);
v___x_1101_ = v___x_1095_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_self_1077_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_next_1078_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_root_1079_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_congr_1080_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_target_x3f_1081_);
lean_ctor_set(v_reuseFailAlloc_1105_, 5, v_proof_x3f_1082_);
lean_ctor_set(v_reuseFailAlloc_1105_, 6, v_size_1084_);
lean_ctor_set(v_reuseFailAlloc_1105_, 7, v_idx_1089_);
lean_ctor_set(v_reuseFailAlloc_1105_, 8, v_generation_1090_);
lean_ctor_set(v_reuseFailAlloc_1105_, 9, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1105_, 10, v_sTerms_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*11, v_flipped_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*11 + 1, v_interpreted_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*11 + 2, v_ctor_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*11 + 3, v_hasLambdas_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*11 + 4, v_heqProofs_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*11 + 5, v_funCC_1093_);
v___x_1101_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; 
lean_inc(v_head_1072_);
v___x_1102_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1072_, v___x_1101_, v___y_1060_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; 
lean_dec_ref(v___x_1102_);
v___x_1103_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1072_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v_head_1072_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_dec_ref(v___x_1103_);
v_as_x27_1058_ = v_tail_1073_;
v_b_1059_ = v___x_1097_;
goto _start;
}
else
{
lean_dec(v_tail_1073_);
lean_dec(v___x_1057_);
return v___x_1103_;
}
}
else
{
lean_dec(v_tail_1073_);
lean_dec(v_head_1072_);
lean_dec(v___x_1057_);
return v___x_1102_;
}
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v_tail_1073_);
lean_dec(v_head_1072_);
lean_dec(v___x_1057_);
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
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1233_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1234_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1235_ = l_Lean_Name_append(v___x_1234_, v___x_1233_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__3));
v___x_1238_ = l_Lean_stringToMessageData(v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_lams_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1360_; 
v_fst_1254_ = lean_ctor_get(v_b_1242_, 0);
v_snd_1255_ = lean_ctor_get(v_b_1242_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_b_1242_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1257_ = v_b_1242_;
v_isShared_1258_ = v_isSharedCheck_1360_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_snd_1255_);
lean_inc(v_fst_1254_);
lean_dec(v_b_1242_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1360_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v_options_1333_; uint8_t v_hasTrace_1334_; 
v_options_1333_ = lean_ctor_get(v___y_1251_, 2);
v_hasTrace_1334_ = lean_ctor_get_uint8(v_options_1333_, sizeof(void*)*1);
if (v_hasTrace_1334_ == 0)
{
v___y_1302_ = v___y_1243_;
v___y_1303_ = v___y_1244_;
v___y_1304_ = v___y_1245_;
v___y_1305_ = v___y_1246_;
v___y_1306_ = v___y_1247_;
v___y_1307_ = v___y_1248_;
v___y_1308_ = v___y_1249_;
v___y_1309_ = v___y_1250_;
v___y_1310_ = v___y_1251_;
v___y_1311_ = v___y_1252_;
goto v___jp_1301_;
}
else
{
lean_object* v_inheritedTraceOptions_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_inheritedTraceOptions_1335_ = lean_ctor_get(v___y_1251_, 13);
v___x_1336_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1337_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1338_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1335_, v_options_1333_, v___x_1337_);
if (v___x_1338_ == 0)
{
v___y_1302_ = v___y_1243_;
v___y_1303_ = v___y_1244_;
v___y_1304_ = v___y_1245_;
v___y_1305_ = v___y_1246_;
v___y_1306_ = v___y_1247_;
v___y_1307_ = v___y_1248_;
v___y_1308_ = v___y_1249_;
v___y_1309_ = v___y_1250_;
v___y_1310_ = v___y_1251_;
v___y_1311_ = v___y_1252_;
goto v___jp_1301_;
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_Meta_Grind_updateLastTag(v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref(v___x_1339_);
v___x_1340_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__4);
lean_inc(v_snd_1255_);
v___x_1341_ = l_Lean_MessageData_ofExpr(v_snd_1255_);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1336_, v___x_1342_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_dec_ref(v___x_1343_);
v___y_1302_ = v___y_1243_;
v___y_1303_ = v___y_1244_;
v___y_1304_ = v___y_1245_;
v___y_1305_ = v___y_1246_;
v___y_1306_ = v___y_1247_;
v___y_1307_ = v___y_1248_;
v___y_1308_ = v___y_1249_;
v___y_1309_ = v___y_1250_;
v___y_1310_ = v___y_1251_;
v___y_1311_ = v___y_1252_;
goto v___jp_1301_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
lean_dec(v_fst_1254_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
lean_dec(v_fst_1254_);
v_a_1352_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1339_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1339_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
v___jp_1259_:
{
if (lean_obj_tag(v_snd_1255_) == 5)
{
lean_object* v_fn_1270_; lean_object* v_arg_1271_; lean_object* v___x_1272_; 
v_fn_1270_ = lean_ctor_get(v_snd_1255_, 0);
lean_inc_ref(v_fn_1270_);
v_arg_1271_ = lean_ctor_get(v_snd_1255_, 1);
lean_inc_ref(v_arg_1271_);
v___x_1272_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1239_, v___y_1260_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = lean_box(0);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___y_1263_);
lean_inc_ref(v___y_1262_);
lean_inc(v___y_1261_);
lean_inc(v___y_1260_);
v___x_1275_ = lean_grind_internalize(v_snd_1255_, v_a_1273_, v___x_1274_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
lean_dec_ref(v___x_1275_);
v___x_1276_ = lean_array_push(v_fst_1254_, v_arg_1271_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_fn_1270_);
lean_ctor_set(v___x_1257_, 0, v___x_1276_);
v___x_1278_ = v___x_1257_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_fn_1270_);
v___x_1278_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
v_b_1242_ = v___x_1278_;
goto _start;
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_arg_1271_);
lean_dec_ref(v_fn_1270_);
lean_del_object(v___x_1257_);
lean_dec(v_fst_1254_);
v_a_1281_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1275_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1275_);
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
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_arg_1271_);
lean_dec_ref(v_fn_1270_);
lean_dec_ref(v_snd_1255_);
lean_del_object(v___x_1257_);
lean_dec(v_fst_1254_);
v_a_1289_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1272_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1272_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_object* v___x_1298_; 
if (v_isShared_1258_ == 0)
{
v___x_1298_ = v___x_1257_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_fst_1254_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_snd_1255_);
v___x_1298_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
}
v___jp_1301_:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1255_, v_a_1240_, v___y_1302_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; uint8_t v___x_1314_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref(v___x_1312_);
v___x_1314_ = lean_unbox(v_a_1313_);
lean_dec(v_a_1313_);
if (v___x_1314_ == 0)
{
v___y_1260_ = v___y_1302_;
v___y_1261_ = v___y_1303_;
v___y_1262_ = v___y_1304_;
v___y_1263_ = v___y_1305_;
v___y_1264_ = v___y_1306_;
v___y_1265_ = v___y_1307_;
v___y_1266_ = v___y_1308_;
v___y_1267_ = v___y_1309_;
v___y_1268_ = v___y_1310_;
v___y_1269_ = v___y_1311_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_inc(v_fst_1254_);
v___x_1315_ = l_Array_reverse___redArg(v_fst_1254_);
lean_inc(v_snd_1255_);
v___x_1316_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1241_, v_snd_1255_, v___x_1315_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_dec_ref(v___x_1316_);
v___y_1260_ = v___y_1302_;
v___y_1261_ = v___y_1303_;
v___y_1262_ = v___y_1304_;
v___y_1263_ = v___y_1305_;
v___y_1264_ = v___y_1306_;
v___y_1265_ = v___y_1307_;
v___y_1266_ = v___y_1308_;
v___y_1267_ = v___y_1309_;
v___y_1268_ = v___y_1310_;
v___y_1269_ = v___y_1311_;
goto v___jp_1259_;
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
lean_dec(v_fst_1254_);
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_del_object(v___x_1257_);
lean_dec(v_snd_1255_);
lean_dec(v_fst_1254_);
v_a_1325_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1312_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1312_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_lams_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1361_, v_a_1362_, v_lams_1363_, v_b_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v_lams_1363_);
lean_dec_ref(v_a_1362_);
lean_dec_ref(v_a_1361_);
return v_res_1376_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1381_ = l_Lean_stringToMessageData(v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1382_, lean_object* v_lams_1383_, lean_object* v_as_x27_1384_, lean_object* v_b_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
if (lean_obj_tag(v_as_x27_1384_) == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_b_1385_);
return v___x_1397_;
}
else
{
lean_object* v_options_1398_; lean_object* v_head_1399_; lean_object* v_tail_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1443_; 
v_options_1398_ = lean_ctor_get(v___y_1394_, 2);
v_head_1399_ = lean_ctor_get(v_as_x27_1384_, 0);
v_tail_1400_ = lean_ctor_get(v_as_x27_1384_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_as_x27_1384_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1402_ = v_as_x27_1384_;
v_isShared_1403_ = v_isSharedCheck_1443_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_tail_1400_);
lean_inc(v_head_1399_);
lean_dec(v_as_x27_1384_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1443_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v_inheritedTraceOptions_1404_; uint8_t v_hasTrace_1405_; lean_object* v___x_1406_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___x_1432_; uint8_t v_a_1434_; 
v_inheritedTraceOptions_1404_ = lean_ctor_get(v___y_1394_, 13);
v_hasTrace_1405_ = lean_ctor_get_uint8(v_options_1398_, sizeof(void*)*1);
v___x_1406_ = lean_box(0);
v___x_1432_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
if (v_hasTrace_1405_ == 0)
{
v_a_1434_ = v_hasTrace_1405_;
goto v___jp_1433_;
}
else
{
lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1442_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1404_, v_options_1398_, v___x_1441_);
v_a_1434_ = v___x_1442_;
goto v___jp_1433_;
}
v___jp_1407_:
{
lean_object* v___x_1420_; 
lean_inc(v_head_1399_);
lean_inc_ref(v___y_1408_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 0);
lean_ctor_set(v___x_1402_, 1, v_head_1399_);
lean_ctor_set(v___x_1402_, 0, v___y_1408_);
v___x_1420_ = v___x_1402_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___y_1408_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_head_1399_);
v___x_1420_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; 
v___x_1421_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_head_1399_, v_a_1382_, v_lams_1383_, v___x_1420_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v_head_1399_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_dec_ref(v___x_1421_);
v_as_x27_1384_ = v_tail_1400_;
v_b_1385_ = v___x_1406_;
goto _start;
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_tail_1400_);
v_a_1423_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1421_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1421_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
v___jp_1433_:
{
lean_object* v___x_1435_; 
v___x_1435_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1434_ == 0)
{
v___y_1408_ = v___x_1435_;
v___y_1409_ = v___y_1386_;
v___y_1410_ = v___y_1387_;
v___y_1411_ = v___y_1388_;
v___y_1412_ = v___y_1389_;
v___y_1413_ = v___y_1390_;
v___y_1414_ = v___y_1391_;
v___y_1415_ = v___y_1392_;
v___y_1416_ = v___y_1393_;
v___y_1417_ = v___y_1394_;
v___y_1418_ = v___y_1395_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_Meta_Grind_updateLastTag(v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec_ref(v___x_1436_);
v___x_1437_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1399_);
v___x_1438_ = l_Lean_MessageData_ofExpr(v_head_1399_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1432_, v___x_1439_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_dec_ref(v___x_1440_);
v___y_1408_ = v___x_1435_;
v___y_1409_ = v___y_1386_;
v___y_1410_ = v___y_1387_;
v___y_1411_ = v___y_1388_;
v___y_1412_ = v___y_1389_;
v___y_1413_ = v___y_1390_;
v___y_1414_ = v___y_1391_;
v___y_1415_ = v___y_1392_;
v___y_1416_ = v___y_1393_;
v___y_1417_ = v___y_1394_;
v___y_1418_ = v___y_1395_;
goto v___jp_1407_;
}
else
{
lean_del_object(v___x_1402_);
lean_dec(v_tail_1400_);
lean_dec(v_head_1399_);
return v___x_1440_;
}
}
else
{
lean_del_object(v___x_1402_);
lean_dec(v_tail_1400_);
lean_dec(v_head_1399_);
return v___x_1436_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1444_, lean_object* v_lams_1445_, lean_object* v_as_x27_1446_, lean_object* v_b_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1444_, v_lams_1445_, v_as_x27_1446_, v_b_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v_lams_1445_);
lean_dec_ref(v_a_1444_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1460_, lean_object* v_lams_1461_, lean_object* v_as_1462_, lean_object* v_as_x27_1463_, lean_object* v_b_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
if (lean_obj_tag(v_as_x27_1463_) == 0)
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_b_1464_);
return v___x_1476_;
}
else
{
lean_object* v_options_1477_; lean_object* v_head_1478_; lean_object* v_tail_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1522_; 
v_options_1477_ = lean_ctor_get(v___y_1473_, 2);
v_head_1478_ = lean_ctor_get(v_as_x27_1463_, 0);
v_tail_1479_ = lean_ctor_get(v_as_x27_1463_, 1);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_as_x27_1463_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1481_ = v_as_x27_1463_;
v_isShared_1482_ = v_isSharedCheck_1522_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_tail_1479_);
lean_inc(v_head_1478_);
lean_dec(v_as_x27_1463_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1522_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_inheritedTraceOptions_1483_; uint8_t v_hasTrace_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; uint8_t v_a_1513_; 
v_inheritedTraceOptions_1483_ = lean_ctor_get(v___y_1473_, 13);
v_hasTrace_1484_ = lean_ctor_get_uint8(v_options_1477_, sizeof(void*)*1);
v___x_1485_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1486_ = lean_box(0);
if (v_hasTrace_1484_ == 0)
{
v_a_1513_ = v_hasTrace_1484_;
goto v___jp_1512_;
}
else
{
lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1520_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1521_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1483_, v_options_1477_, v___x_1520_);
v_a_1513_ = v___x_1521_;
goto v___jp_1512_;
}
v___jp_1487_:
{
lean_object* v___x_1500_; 
lean_inc(v_head_1478_);
lean_inc_ref(v___y_1488_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set_tag(v___x_1481_, 0);
lean_ctor_set(v___x_1481_, 1, v_head_1478_);
lean_ctor_set(v___x_1481_, 0, v___y_1488_);
v___x_1500_ = v___x_1481_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___y_1488_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_head_1478_);
v___x_1500_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; 
v___x_1501_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_head_1478_, v_a_1460_, v_lams_1461_, v___x_1500_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v_head_1478_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v___x_1502_; 
lean_dec_ref(v___x_1501_);
v___x_1502_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1460_, v_lams_1461_, v_tail_1479_, v___x_1486_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1502_;
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_tail_1479_);
v_a_1503_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1501_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1501_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
v___jp_1512_:
{
lean_object* v___x_1514_; 
v___x_1514_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1513_ == 0)
{
v___y_1488_ = v___x_1514_;
v___y_1489_ = v___y_1465_;
v___y_1490_ = v___y_1466_;
v___y_1491_ = v___y_1467_;
v___y_1492_ = v___y_1468_;
v___y_1493_ = v___y_1469_;
v___y_1494_ = v___y_1470_;
v___y_1495_ = v___y_1471_;
v___y_1496_ = v___y_1472_;
v___y_1497_ = v___y_1473_;
v___y_1498_ = v___y_1474_;
goto v___jp_1487_;
}
else
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_Meta_Grind_updateLastTag(v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref(v___x_1515_);
v___x_1516_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1478_);
v___x_1517_ = l_Lean_MessageData_ofExpr(v_head_1478_);
v___x_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1516_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1485_, v___x_1518_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_dec_ref(v___x_1519_);
v___y_1488_ = v___x_1514_;
v___y_1489_ = v___y_1465_;
v___y_1490_ = v___y_1466_;
v___y_1491_ = v___y_1467_;
v___y_1492_ = v___y_1468_;
v___y_1493_ = v___y_1469_;
v___y_1494_ = v___y_1470_;
v___y_1495_ = v___y_1471_;
v___y_1496_ = v___y_1472_;
v___y_1497_ = v___y_1473_;
v___y_1498_ = v___y_1474_;
goto v___jp_1487_;
}
else
{
lean_del_object(v___x_1481_);
lean_dec(v_tail_1479_);
lean_dec(v_head_1478_);
return v___x_1519_;
}
}
else
{
lean_del_object(v___x_1481_);
lean_dec(v_tail_1479_);
lean_dec(v_head_1478_);
return v___x_1515_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1523_, lean_object* v_lams_1524_, lean_object* v_as_1525_, lean_object* v_as_x27_1526_, lean_object* v_b_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1523_, v_lams_1524_, v_as_1525_, v_as_x27_1526_, v_b_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec(v_as_1525_);
lean_dec_ref(v_lams_1524_);
lean_dec_ref(v_a_1523_);
return v_res_1539_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1545_ = l_Lean_stringToMessageData(v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1546_, lean_object* v_lams_1547_, lean_object* v_as_1548_, size_t v_sz_1549_, size_t v_i_1550_, lean_object* v_b_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_usize_dec_lt(v_i_1550_, v_sz_1549_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_b_1551_);
return v___x_1564_;
}
else
{
lean_object* v_options_1565_; lean_object* v_inheritedTraceOptions_1566_; uint8_t v_hasTrace_1567_; lean_object* v___x_1568_; lean_object* v_a_1569_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; 
v_options_1565_ = lean_ctor_get(v___y_1560_, 2);
v_inheritedTraceOptions_1566_ = lean_ctor_get(v___y_1560_, 13);
v_hasTrace_1567_ = lean_ctor_get_uint8(v_options_1565_, sizeof(void*)*1);
v___x_1568_ = lean_box(0);
v_a_1569_ = lean_array_uget_borrowed(v_as_1548_, v_i_1550_);
if (v_hasTrace_1567_ == 0)
{
v___y_1571_ = v___y_1552_;
v___y_1572_ = v___y_1553_;
v___y_1573_ = v___y_1554_;
v___y_1574_ = v___y_1555_;
v___y_1575_ = v___y_1556_;
v___y_1576_ = v___y_1557_;
v___y_1577_ = v___y_1558_;
v___y_1578_ = v___y_1559_;
v___y_1579_ = v___y_1560_;
v___y_1580_ = v___y_1561_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1596_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1597_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1598_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1566_, v_options_1565_, v___x_1597_);
if (v___x_1598_ == 0)
{
v___y_1571_ = v___y_1552_;
v___y_1572_ = v___y_1553_;
v___y_1573_ = v___y_1554_;
v___y_1574_ = v___y_1555_;
v___y_1575_ = v___y_1556_;
v___y_1576_ = v___y_1557_;
v___y_1577_ = v___y_1558_;
v___y_1578_ = v___y_1559_;
v___y_1579_ = v___y_1560_;
v___y_1580_ = v___y_1561_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Meta_Grind_updateLastTag(v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1600_; 
lean_dec_ref(v___x_1599_);
v___x_1600_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1569_, v___y_1552_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1569_);
v___x_1603_ = l_Lean_MessageData_ofExpr(v_a_1569_);
v___x_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1601_);
lean_dec(v_a_1601_);
v___x_1608_ = lean_box(0);
v___x_1609_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1607_, v___x_1608_);
v___x_1610_ = l_Lean_MessageData_ofList(v___x_1609_);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1606_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1596_, v___x_1611_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_dec_ref(v___x_1612_);
v___y_1571_ = v___y_1552_;
v___y_1572_ = v___y_1553_;
v___y_1573_ = v___y_1554_;
v___y_1574_ = v___y_1555_;
v___y_1575_ = v___y_1556_;
v___y_1576_ = v___y_1557_;
v___y_1577_ = v___y_1558_;
v___y_1578_ = v___y_1559_;
v___y_1579_ = v___y_1560_;
v___y_1580_ = v___y_1561_;
goto v___jp_1570_;
}
else
{
return v___x_1612_;
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_a_1613_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1600_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1600_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
return v___x_1599_;
}
}
}
v___jp_1570_:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1569_, v___y_1571_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref(v___x_1581_);
v___x_1583_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1582_);
lean_dec(v_a_1582_);
lean_inc(v___x_1583_);
v___x_1584_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1546_, v_lams_1547_, v___x_1583_, v___x_1583_, v___x_1568_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___x_1583_);
if (lean_obj_tag(v___x_1584_) == 0)
{
size_t v___x_1585_; size_t v___x_1586_; 
lean_dec_ref(v___x_1584_);
v___x_1585_ = ((size_t)1ULL);
v___x_1586_ = lean_usize_add(v_i_1550_, v___x_1585_);
v_i_1550_ = v___x_1586_;
v_b_1551_ = v___x_1568_;
goto _start;
}
else
{
return v___x_1584_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_a_1588_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1581_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1581_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1621_ = _args[0];
lean_object* v_lams_1622_ = _args[1];
lean_object* v_as_1623_ = _args[2];
lean_object* v_sz_1624_ = _args[3];
lean_object* v_i_1625_ = _args[4];
lean_object* v_b_1626_ = _args[5];
lean_object* v___y_1627_ = _args[6];
lean_object* v___y_1628_ = _args[7];
lean_object* v___y_1629_ = _args[8];
lean_object* v___y_1630_ = _args[9];
lean_object* v___y_1631_ = _args[10];
lean_object* v___y_1632_ = _args[11];
lean_object* v___y_1633_ = _args[12];
lean_object* v___y_1634_ = _args[13];
lean_object* v___y_1635_ = _args[14];
lean_object* v___y_1636_ = _args[15];
lean_object* v___y_1637_ = _args[16];
_start:
{
size_t v_sz_boxed_1638_; size_t v_i_boxed_1639_; lean_object* v_res_1640_; 
v_sz_boxed_1638_ = lean_unbox_usize(v_sz_1624_);
lean_dec(v_sz_1624_);
v_i_boxed_1639_ = lean_unbox_usize(v_i_1625_);
lean_dec(v_i_1625_);
v_res_1640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1621_, v_lams_1622_, v_as_1623_, v_sz_boxed_1638_, v_i_boxed_1639_, v_b_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v_as_1623_);
lean_dec_ref(v_lams_1622_);
lean_dec_ref(v_a_1621_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1641_, lean_object* v_lams_1642_, lean_object* v_as_1643_, size_t v_sz_1644_, size_t v_i_1645_, lean_object* v_b_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
uint8_t v___x_1658_; 
v___x_1658_ = lean_usize_dec_lt(v_i_1645_, v_sz_1644_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_b_1646_);
return v___x_1659_;
}
else
{
lean_object* v_options_1660_; lean_object* v_inheritedTraceOptions_1661_; uint8_t v_hasTrace_1662_; lean_object* v___x_1663_; lean_object* v_a_1664_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; 
v_options_1660_ = lean_ctor_get(v___y_1655_, 2);
v_inheritedTraceOptions_1661_ = lean_ctor_get(v___y_1655_, 13);
v_hasTrace_1662_ = lean_ctor_get_uint8(v_options_1660_, sizeof(void*)*1);
v___x_1663_ = lean_box(0);
v_a_1664_ = lean_array_uget_borrowed(v_as_1643_, v_i_1645_);
if (v_hasTrace_1662_ == 0)
{
v___y_1666_ = v___y_1647_;
v___y_1667_ = v___y_1648_;
v___y_1668_ = v___y_1649_;
v___y_1669_ = v___y_1650_;
v___y_1670_ = v___y_1651_;
v___y_1671_ = v___y_1652_;
v___y_1672_ = v___y_1653_;
v___y_1673_ = v___y_1654_;
v___y_1674_ = v___y_1655_;
v___y_1675_ = v___y_1656_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1691_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1692_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1693_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1661_, v_options_1660_, v___x_1692_);
if (v___x_1693_ == 0)
{
v___y_1666_ = v___y_1647_;
v___y_1667_ = v___y_1648_;
v___y_1668_ = v___y_1649_;
v___y_1669_ = v___y_1650_;
v___y_1670_ = v___y_1651_;
v___y_1671_ = v___y_1652_;
v___y_1672_ = v___y_1653_;
v___y_1673_ = v___y_1654_;
v___y_1674_ = v___y_1655_;
v___y_1675_ = v___y_1656_;
goto v___jp_1665_;
}
else
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_Meta_Grind_updateLastTag(v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v___x_1695_; 
lean_dec_ref(v___x_1694_);
v___x_1695_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1664_, v___y_1647_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1664_);
v___x_1698_ = l_Lean_MessageData_ofExpr(v_a_1664_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1696_);
lean_dec(v_a_1696_);
v___x_1703_ = lean_box(0);
v___x_1704_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1702_, v___x_1703_);
v___x_1705_ = l_Lean_MessageData_ofList(v___x_1704_);
v___x_1706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1701_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1691_, v___x_1706_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_dec_ref(v___x_1707_);
v___y_1666_ = v___y_1647_;
v___y_1667_ = v___y_1648_;
v___y_1668_ = v___y_1649_;
v___y_1669_ = v___y_1650_;
v___y_1670_ = v___y_1651_;
v___y_1671_ = v___y_1652_;
v___y_1672_ = v___y_1653_;
v___y_1673_ = v___y_1654_;
v___y_1674_ = v___y_1655_;
v___y_1675_ = v___y_1656_;
goto v___jp_1665_;
}
else
{
return v___x_1707_;
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_a_1708_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1695_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1695_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
else
{
return v___x_1694_;
}
}
}
v___jp_1665_:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1664_, v___y_1666_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref(v___x_1676_);
v___x_1678_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1677_);
lean_dec(v_a_1677_);
lean_inc(v___x_1678_);
v___x_1679_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1641_, v_lams_1642_, v___x_1678_, v___x_1678_, v___x_1663_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___x_1678_);
if (lean_obj_tag(v___x_1679_) == 0)
{
size_t v___x_1680_; size_t v___x_1681_; lean_object* v___x_1682_; 
lean_dec_ref(v___x_1679_);
v___x_1680_ = ((size_t)1ULL);
v___x_1681_ = lean_usize_add(v_i_1645_, v___x_1680_);
v___x_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1641_, v_lams_1642_, v_as_1643_, v_sz_1644_, v___x_1681_, v___x_1663_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
return v___x_1682_;
}
else
{
return v___x_1679_;
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_a_1683_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1676_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1676_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1716_ = _args[0];
lean_object* v_lams_1717_ = _args[1];
lean_object* v_as_1718_ = _args[2];
lean_object* v_sz_1719_ = _args[3];
lean_object* v_i_1720_ = _args[4];
lean_object* v_b_1721_ = _args[5];
lean_object* v___y_1722_ = _args[6];
lean_object* v___y_1723_ = _args[7];
lean_object* v___y_1724_ = _args[8];
lean_object* v___y_1725_ = _args[9];
lean_object* v___y_1726_ = _args[10];
lean_object* v___y_1727_ = _args[11];
lean_object* v___y_1728_ = _args[12];
lean_object* v___y_1729_ = _args[13];
lean_object* v___y_1730_ = _args[14];
lean_object* v___y_1731_ = _args[15];
lean_object* v___y_1732_ = _args[16];
_start:
{
size_t v_sz_boxed_1733_; size_t v_i_boxed_1734_; lean_object* v_res_1735_; 
v_sz_boxed_1733_ = lean_unbox_usize(v_sz_1719_);
lean_dec(v_sz_1719_);
v_i_boxed_1734_ = lean_unbox_usize(v_i_1720_);
lean_dec(v_i_1720_);
v_res_1735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1716_, v_lams_1717_, v_as_1718_, v_sz_boxed_1733_, v_i_boxed_1734_, v_b_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v_as_1718_);
lean_dec_ref(v_lams_1717_);
lean_dec_ref(v_a_1716_);
return v_res_1735_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1738_ = l_Lean_stringToMessageData(v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1741_ = l_Lean_stringToMessageData(v___x_1740_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1742_, lean_object* v_fns_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1755_ = lean_array_get_size(v_lams_1742_);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_nat_dec_eq(v___x_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1758_ = lean_st_ref_get(v_a_1744_);
v___x_1759_ = l_Lean_instInhabitedExpr;
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_nat_sub(v___x_1755_, v___x_1760_);
v___x_1762_ = lean_array_get_borrowed(v___x_1759_, v_lams_1742_, v___x_1761_);
lean_dec(v___x_1761_);
lean_inc(v___x_1762_);
v___x_1763_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1758_, v___x_1762_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v_options_1788_; uint8_t v_hasTrace_1789_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
v_options_1788_ = lean_ctor_get(v_a_1752_, 2);
v_hasTrace_1789_ = lean_ctor_get_uint8(v_options_1788_, sizeof(void*)*1);
if (v_hasTrace_1789_ == 0)
{
v___y_1766_ = v_a_1744_;
v___y_1767_ = v_a_1745_;
v___y_1768_ = v_a_1746_;
v___y_1769_ = v_a_1747_;
v___y_1770_ = v_a_1748_;
v___y_1771_ = v_a_1749_;
v___y_1772_ = v_a_1750_;
v___y_1773_ = v_a_1751_;
v___y_1774_ = v_a_1752_;
v___y_1775_ = v_a_1753_;
goto v___jp_1765_;
}
else
{
lean_object* v_inheritedTraceOptions_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_inheritedTraceOptions_1790_ = lean_ctor_get(v_a_1752_, 13);
v___x_1791_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__1));
v___x_1792_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_Grind_propagateBeta_spec__0___closed__2);
v___x_1793_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1790_, v_options_1788_, v___x_1792_);
if (v___x_1793_ == 0)
{
v___y_1766_ = v_a_1744_;
v___y_1767_ = v_a_1745_;
v___y_1768_ = v_a_1746_;
v___y_1769_ = v_a_1747_;
v___y_1770_ = v_a_1748_;
v___y_1771_ = v_a_1749_;
v___y_1772_ = v_a_1750_;
v___y_1773_ = v_a_1751_;
v___y_1774_ = v_a_1752_;
v___y_1775_ = v_a_1753_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Meta_Grind_updateLastTag(v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec_ref(v___x_1794_);
v___x_1795_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1743_);
v___x_1796_ = lean_array_to_list(v_fns_1743_);
v___x_1797_ = lean_box(0);
v___x_1798_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1796_, v___x_1797_);
v___x_1799_ = l_Lean_MessageData_ofList(v___x_1798_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1795_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___x_1801_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
lean_inc_ref(v_lams_1742_);
v___x_1803_ = lean_array_to_list(v_lams_1742_);
v___x_1804_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1803_, v___x_1797_);
v___x_1805_ = l_Lean_MessageData_ofList(v___x_1804_);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1802_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1791_, v___x_1806_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_dec_ref(v___x_1807_);
v___y_1766_ = v_a_1744_;
v___y_1767_ = v_a_1745_;
v___y_1768_ = v_a_1746_;
v___y_1769_ = v_a_1747_;
v___y_1770_ = v_a_1748_;
v___y_1771_ = v_a_1749_;
v___y_1772_ = v_a_1750_;
v___y_1773_ = v_a_1751_;
v___y_1774_ = v_a_1752_;
v___y_1775_ = v_a_1753_;
goto v___jp_1765_;
}
else
{
lean_dec(v_a_1764_);
lean_dec_ref(v_fns_1743_);
lean_dec_ref(v_lams_1742_);
return v___x_1807_;
}
}
else
{
lean_dec(v_a_1764_);
lean_dec_ref(v_fns_1743_);
lean_dec_ref(v_lams_1742_);
return v___x_1794_;
}
}
}
v___jp_1765_:
{
lean_object* v___x_1776_; size_t v_sz_1777_; size_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = lean_box(0);
v_sz_1777_ = lean_array_size(v_fns_1743_);
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1764_, v_lams_1742_, v_fns_1743_, v_sz_1777_, v___x_1778_, v___x_1776_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec_ref(v_fns_1743_);
lean_dec_ref(v_lams_1742_);
lean_dec(v_a_1764_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v___x_1779_, 0);
lean_dec(v_unused_1787_);
v___x_1781_ = v___x_1779_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_dec(v___x_1779_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1776_);
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1776_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
return v___x_1779_;
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v_fns_1743_);
lean_dec_ref(v_lams_1742_);
v_a_1808_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1763_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1763_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec_ref(v_fns_1743_);
lean_dec_ref(v_lams_1742_);
v___x_1816_ = lean_box(0);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1818_, lean_object* v_fns_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1818_, v_fns_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec(v_a_1820_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1832_, lean_object* v_lams_1833_, lean_object* v_as_1834_, lean_object* v_as_x27_1835_, lean_object* v_b_1836_, lean_object* v_a_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1832_, v_lams_1833_, v_as_1834_, v_as_x27_1835_, v_b_1836_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1850_ = _args[0];
lean_object* v_lams_1851_ = _args[1];
lean_object* v_as_1852_ = _args[2];
lean_object* v_as_x27_1853_ = _args[3];
lean_object* v_b_1854_ = _args[4];
lean_object* v_a_1855_ = _args[5];
lean_object* v___y_1856_ = _args[6];
lean_object* v___y_1857_ = _args[7];
lean_object* v___y_1858_ = _args[8];
lean_object* v___y_1859_ = _args[9];
lean_object* v___y_1860_ = _args[10];
lean_object* v___y_1861_ = _args[11];
lean_object* v___y_1862_ = _args[12];
lean_object* v___y_1863_ = _args[13];
lean_object* v___y_1864_ = _args[14];
lean_object* v___y_1865_ = _args[15];
lean_object* v___y_1866_ = _args[16];
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1850_, v_lams_1851_, v_as_1852_, v_as_x27_1853_, v_b_1854_, v_a_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v_as_1852_);
lean_dec_ref(v_lams_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1868_, lean_object* v_lams_1869_, lean_object* v_as_1870_, lean_object* v_as_x27_1871_, lean_object* v_b_1872_, lean_object* v_a_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1868_, v_lams_1869_, v_as_x27_1871_, v_b_1872_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1886_ = _args[0];
lean_object* v_lams_1887_ = _args[1];
lean_object* v_as_1888_ = _args[2];
lean_object* v_as_x27_1889_ = _args[3];
lean_object* v_b_1890_ = _args[4];
lean_object* v_a_1891_ = _args[5];
lean_object* v___y_1892_ = _args[6];
lean_object* v___y_1893_ = _args[7];
lean_object* v___y_1894_ = _args[8];
lean_object* v___y_1895_ = _args[9];
lean_object* v___y_1896_ = _args[10];
lean_object* v___y_1897_ = _args[11];
lean_object* v___y_1898_ = _args[12];
lean_object* v___y_1899_ = _args[13];
lean_object* v___y_1900_ = _args[14];
lean_object* v___y_1901_ = _args[15];
lean_object* v___y_1902_ = _args[16];
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1886_, v_lams_1887_, v_as_1888_, v_as_x27_1889_, v_b_1890_, v_a_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
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
lean_dec(v_as_1888_);
lean_dec_ref(v_lams_1887_);
lean_dec_ref(v_a_1886_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1907_, lean_object* v_as_1908_, size_t v_sz_1909_, size_t v_i_1910_, lean_object* v_b_1911_){
_start:
{
lean_object* v_a_1913_; uint8_t v___x_1917_; 
v___x_1917_ = lean_usize_dec_lt(v_i_1910_, v_sz_1909_);
if (v___x_1917_ == 0)
{
lean_inc_ref(v_b_1911_);
return v_b_1911_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v_a_1920_; 
v___x_1918_ = lean_box(0);
v___x_1919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1920_ = lean_array_uget_borrowed(v_as_1908_, v_i_1910_);
if (lean_obj_tag(v_a_1920_) == 6)
{
lean_object* v_binderType_1921_; uint8_t v___x_1922_; 
v_binderType_1921_ = lean_ctor_get(v_a_1920_, 1);
v___x_1922_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_d_1907_, v_binderType_1921_);
if (v___x_1922_ == 0)
{
v_a_1913_ = v___x_1919_;
goto v___jp_1912_;
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_inc_ref(v_a_1920_);
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_a_1920_);
v___x_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v___x_1918_);
return v___x_1925_;
}
}
else
{
v_a_1913_ = v___x_1919_;
goto v___jp_1912_;
}
}
v___jp_1912_:
{
size_t v___x_1914_; size_t v___x_1915_; 
v___x_1914_ = ((size_t)1ULL);
v___x_1915_ = lean_usize_add(v_i_1910_, v___x_1914_);
v_i_1910_ = v___x_1915_;
v_b_1911_ = v_a_1913_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_1926_, lean_object* v_as_1927_, lean_object* v_sz_1928_, lean_object* v_i_1929_, lean_object* v_b_1930_){
_start:
{
size_t v_sz_boxed_1931_; size_t v_i_boxed_1932_; lean_object* v_res_1933_; 
v_sz_boxed_1931_ = lean_unbox_usize(v_sz_1928_);
lean_dec(v_sz_1928_);
v_i_boxed_1932_ = lean_unbox_usize(v_i_1929_);
lean_dec(v_i_1929_);
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1926_, v_as_1927_, v_sz_boxed_1931_, v_i_boxed_1932_, v_b_1930_);
lean_dec_ref(v_b_1930_);
lean_dec_ref(v_as_1927_);
lean_dec_ref(v_d_1926_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_1934_, lean_object* v_d_1935_){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; size_t v_sz_1938_; size_t v___x_1939_; lean_object* v___x_1940_; lean_object* v_fst_1941_; 
v___x_1936_ = lean_box(0);
v___x_1937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_1938_ = lean_array_size(v_lams_1934_);
v___x_1939_ = ((size_t)0ULL);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1935_, v_lams_1934_, v_sz_1938_, v___x_1939_, v___x_1937_);
v_fst_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_fst_1941_);
lean_dec_ref(v___x_1940_);
if (lean_obj_tag(v_fst_1941_) == 0)
{
return v___x_1936_;
}
else
{
lean_object* v_val_1942_; 
v_val_1942_ = lean_ctor_get(v_fst_1941_, 0);
lean_inc(v_val_1942_);
lean_dec_ref(v_fst_1941_);
return v_val_1942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_1943_, lean_object* v_d_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_1943_, v_d_1944_);
lean_dec_ref(v_d_1944_);
lean_dec_ref(v_lams_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_1956_, lean_object* v_lams_u2081_1957_, lean_object* v_as_1958_, size_t v_sz_1959_, size_t v_i_1960_, lean_object* v_b_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_a_1974_; uint8_t v___x_1978_; 
v___x_1978_ = lean_usize_dec_lt(v_i_1960_, v_sz_1959_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_b_1961_);
return v___x_1979_;
}
else
{
lean_object* v___x_1980_; lean_object* v_a_1981_; 
v___x_1980_ = lean_box(0);
v_a_1981_ = lean_array_uget_borrowed(v_as_1958_, v_i_1960_);
if (lean_obj_tag(v_a_1981_) == 6)
{
lean_object* v_binderType_1982_; lean_object* v_body_1983_; lean_object* v___x_1984_; 
v_binderType_1982_ = lean_ctor_get(v_a_1981_, 1);
v_body_1983_ = lean_ctor_get(v_a_1981_, 2);
lean_inc_ref(v_binderType_1982_);
v___x_1984_ = l_Lean_Meta_getLevel(v_binderType_1982_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref(v___x_1984_);
v___x_1986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_1987_ = lean_box(0);
v___x_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1988_, 0, v_a_1985_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
lean_inc_ref(v___x_1988_);
v___x_1989_ = l_Lean_mkConst(v___x_1986_, v___x_1988_);
lean_inc_ref(v_binderType_1982_);
v___x_1990_ = l_Lean_Expr_app___override(v___x_1989_, v_binderType_1982_);
v___x_1991_ = lean_box(0);
v___x_1992_ = l_Lean_Meta_synthInstance_x3f(v___x_1990_, v___x_1991_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref(v___x_1992_);
if (lean_obj_tag(v_a_1993_) == 1)
{
lean_object* v_val_1994_; lean_object* v___x_1995_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; uint8_t v___x_2060_; 
v_val_1994_ = lean_ctor_get(v_a_1993_, 0);
lean_inc(v_val_1994_);
lean_dec_ref(v_a_1993_);
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_2060_ = l_Lean_Expr_hasLooseBVars(v_body_1983_);
if (v___x_2060_ == 0)
{
v___y_1997_ = v___y_1962_;
v___y_1998_ = v___y_1963_;
v___y_1999_ = v___y_1964_;
v___y_2000_ = v___y_1965_;
v___y_2001_ = v___y_1966_;
v___y_2002_ = v___y_1967_;
v___y_2003_ = v___y_1968_;
v___y_2004_ = v___y_1969_;
v___y_2005_ = v___y_1970_;
v___y_2006_ = v___y_1971_;
goto v___jp_1996_;
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_1988_);
v___x_2062_ = l_Lean_mkConst(v___x_2061_, v___x_1988_);
lean_inc_ref(v_binderType_1982_);
v___x_2063_ = l_Lean_Expr_app___override(v___x_2062_, v_binderType_1982_);
v___x_2064_ = l_Lean_Meta_synthInstance_x3f(v___x_2063_, v___x_1991_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref(v___x_2064_);
if (lean_obj_tag(v_a_2065_) == 0)
{
lean_dec(v_val_1994_);
lean_dec_ref(v___x_1988_);
v_a_1974_ = v___x_1980_;
goto v___jp_1973_;
}
else
{
lean_dec_ref(v_a_2065_);
if (v___x_2060_ == 0)
{
lean_dec(v_val_1994_);
lean_dec_ref(v___x_1988_);
v_a_1974_ = v___x_1980_;
goto v___jp_1973_;
}
else
{
v___y_1997_ = v___y_1962_;
v___y_1998_ = v___y_1963_;
v___y_1999_ = v___y_1964_;
v___y_2000_ = v___y_1965_;
v___y_2001_ = v___y_1966_;
v___y_2002_ = v___y_1967_;
v___y_2003_ = v___y_1968_;
v___y_2004_ = v___y_1969_;
v___y_2005_ = v___y_1970_;
v___y_2006_ = v___y_1971_;
goto v___jp_1996_;
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_val_1994_);
lean_dec_ref(v___x_1988_);
v_a_2066_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2064_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2064_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
v___jp_1996_:
{
lean_object* v___x_2007_; 
v___x_2007_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_1956_, v_binderType_1982_);
if (lean_obj_tag(v___x_2007_) == 1)
{
lean_object* v_val_2008_; 
v_val_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_val_2008_);
lean_dec_ref(v___x_2007_);
if (lean_obj_tag(v_val_2008_) == 6)
{
lean_object* v_binderType_2009_; lean_object* v_body_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_binderType_2009_ = lean_ctor_get(v_val_2008_, 1);
lean_inc_ref(v_binderType_2009_);
v_body_2010_ = lean_ctor_get(v_val_2008_, 2);
lean_inc_ref(v_body_2010_);
lean_dec_ref(v_val_2008_);
v___x_2011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2012_ = l_Lean_mkConst(v___x_2011_, v___x_1988_);
v___x_2013_ = l_Lean_mkAppB(v___x_2012_, v_binderType_2009_, v_val_1994_);
v___x_2014_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2013_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = lean_array_fget_borrowed(v_lams_u2081_1957_, v___x_1995_);
v___x_2017_ = lean_array_fget_borrowed(v_lams_u2082_1956_, v___x_1995_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
lean_inc(v___y_2002_);
lean_inc_ref(v___y_2001_);
lean_inc(v___y_2000_);
lean_inc_ref(v___y_1999_);
lean_inc(v___y_1998_);
lean_inc(v___y_1997_);
lean_inc(v___x_2017_);
lean_inc(v___x_2016_);
v___x_2018_ = lean_grind_mk_eq_proof(v___x_2016_, v___x_2017_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref(v___x_2018_);
v___x_2020_ = lean_expr_instantiate1(v_body_1983_, v_a_2015_);
v___x_2021_ = lean_expr_instantiate1(v_body_2010_, v_a_2015_);
lean_dec_ref(v_body_2010_);
v___x_2022_ = l_Lean_Meta_mkCongrFun(v_a_2019_, v_a_2015_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref(v___x_2022_);
v___x_2024_ = l_Lean_Meta_mkEq(v___x_2020_, v___x_2021_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
v___x_2026_ = l_Lean_Meta_mkExpectedPropHint(v_a_2023_, v_a_2025_);
v___x_2027_ = l_Lean_Meta_Grind_pushNewFact(v___x_2026_, v___x_1995_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_dec_ref(v___x_2027_);
v_a_1974_ = v___x_1980_;
goto v___jp_1973_;
}
else
{
return v___x_2027_;
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_a_2023_);
v_a_2028_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2024_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2024_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v___x_2021_);
lean_dec_ref(v___x_2020_);
v_a_2036_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2022_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2022_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec(v_a_2015_);
lean_dec_ref(v_body_2010_);
v_a_2044_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2018_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2018_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v_body_2010_);
v_a_2052_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2014_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2014_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_dec(v_val_2008_);
lean_dec(v_val_1994_);
lean_dec_ref(v___x_1988_);
v_a_1974_ = v___x_1980_;
goto v___jp_1973_;
}
}
else
{
lean_dec(v___x_2007_);
lean_dec(v_val_1994_);
lean_dec_ref(v___x_1988_);
v_a_1974_ = v___x_1980_;
goto v___jp_1973_;
}
}
}
else
{
lean_dec(v_a_1993_);
lean_dec_ref(v___x_1988_);
v_a_1974_ = v___x_1980_;
goto v___jp_1973_;
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v___x_1988_);
v_a_2074_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_1992_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_1992_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_1984_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_1984_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
v_a_1974_ = v___x_1980_;
goto v___jp_1973_;
}
}
v___jp_1973_:
{
size_t v___x_1975_; size_t v___x_1976_; 
v___x_1975_ = ((size_t)1ULL);
v___x_1976_ = lean_usize_add(v_i_1960_, v___x_1975_);
v_i_1960_ = v___x_1976_;
v_b_1961_ = v_a_1974_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2090_ = _args[0];
lean_object* v_lams_u2081_2091_ = _args[1];
lean_object* v_as_2092_ = _args[2];
lean_object* v_sz_2093_ = _args[3];
lean_object* v_i_2094_ = _args[4];
lean_object* v_b_2095_ = _args[5];
lean_object* v___y_2096_ = _args[6];
lean_object* v___y_2097_ = _args[7];
lean_object* v___y_2098_ = _args[8];
lean_object* v___y_2099_ = _args[9];
lean_object* v___y_2100_ = _args[10];
lean_object* v___y_2101_ = _args[11];
lean_object* v___y_2102_ = _args[12];
lean_object* v___y_2103_ = _args[13];
lean_object* v___y_2104_ = _args[14];
lean_object* v___y_2105_ = _args[15];
lean_object* v___y_2106_ = _args[16];
_start:
{
size_t v_sz_boxed_2107_; size_t v_i_boxed_2108_; lean_object* v_res_2109_; 
v_sz_boxed_2107_ = lean_unbox_usize(v_sz_2093_);
lean_dec(v_sz_2093_);
v_i_boxed_2108_ = lean_unbox_usize(v_i_2094_);
lean_dec(v_i_2094_);
v_res_2109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2090_, v_lams_u2081_2091_, v_as_2092_, v_sz_boxed_2107_, v_i_boxed_2108_, v_b_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v_as_2092_);
lean_dec_ref(v_lams_u2081_2091_);
lean_dec_ref(v_lams_u2082_2090_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2110_, lean_object* v_lams_u2082_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2123_ = lean_array_get_size(v_lams_u2081_2110_);
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = lean_nat_dec_eq(v___x_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = lean_array_get_size(v_lams_u2082_2111_);
v___x_2127_ = lean_nat_dec_eq(v___x_2126_, v___x_2124_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; size_t v_sz_2129_; size_t v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = lean_box(0);
v_sz_2129_ = lean_array_size(v_lams_u2081_2110_);
v___x_2130_ = ((size_t)0ULL);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2111_, v_lams_u2081_2110_, v_lams_u2081_2110_, v_sz_2129_, v___x_2130_, v___x_2128_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2138_ == 0)
{
lean_object* v_unused_2139_; 
v_unused_2139_ = lean_ctor_get(v___x_2131_, 0);
lean_dec(v_unused_2139_);
v___x_2133_ = v___x_2131_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_dec(v___x_2131_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2128_);
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2128_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
else
{
return v___x_2131_;
}
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_box(0);
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
return v___x_2141_;
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_box(0);
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
return v___x_2143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2144_, lean_object* v_lams_u2082_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2144_, v_lams_u2082_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec_ref(v_a_2152_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_lams_u2082_2145_);
lean_dec_ref(v_lams_u2081_2144_);
return v_res_2157_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2158_){
_start:
{
uint8_t v___x_2159_; 
v___x_2159_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2160_){
_start:
{
uint8_t v_res_2161_; lean_object* v_r_2162_; 
v_res_2161_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2160_);
lean_dec_ref(v_x_2160_);
v_r_2162_ = lean_box(v_res_2161_);
return v_r_2162_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2163_, lean_object* v_x_2164_){
_start:
{
uint8_t v___x_2165_; 
v___x_2165_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2166_, lean_object* v_x_2167_){
_start:
{
uint8_t v_res_2168_; lean_object* v_r_2169_; 
v_res_2168_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2166_, v_x_2167_);
lean_dec_ref(v_x_2167_);
v_r_2169_ = lean_box(v_res_2168_);
return v_r_2169_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2170_, lean_object* v_v_2171_, lean_object* v_i_2172_){
_start:
{
lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = lean_array_get_size(v_xs_2170_);
v___x_2174_ = lean_nat_dec_lt(v_i_2172_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; 
lean_dec(v_i_2172_);
v___x_2175_ = lean_box(0);
return v___x_2175_;
}
else
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = lean_array_fget_borrowed(v_xs_2170_, v_i_2172_);
v___x_2177_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2176_, v_v_2171_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_add(v_i_2172_, v___x_2178_);
lean_dec(v_i_2172_);
v_i_2172_ = v___x_2179_;
goto _start;
}
else
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_i_2172_);
return v___x_2181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2182_, lean_object* v_v_2183_, lean_object* v_i_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2182_, v_v_2183_, v_i_2184_);
lean_dec_ref(v_v_2183_);
lean_dec_ref(v_xs_2182_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2186_, lean_object* v_v_2187_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2186_, v_v_2187_, v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2190_, lean_object* v_v_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2190_, v_v_2191_);
lean_dec_ref(v_v_2191_);
lean_dec_ref(v_xs_2190_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2193_, size_t v_x_2194_, lean_object* v_x_2195_){
_start:
{
if (lean_obj_tag(v_x_2193_) == 0)
{
lean_object* v_es_2196_; lean_object* v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; size_t v___x_2200_; lean_object* v_j_2201_; lean_object* v_entry_2202_; 
v_es_2196_ = lean_ctor_get(v_x_2193_, 0);
v___x_2197_ = lean_box(2);
v___x_2198_ = ((size_t)5ULL);
v___x_2199_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2200_ = lean_usize_land(v_x_2194_, v___x_2199_);
v_j_2201_ = lean_usize_to_nat(v___x_2200_);
v_entry_2202_ = lean_array_get(v___x_2197_, v_es_2196_, v_j_2201_);
switch(lean_obj_tag(v_entry_2202_))
{
case 0:
{
lean_object* v_key_2203_; uint8_t v___x_2204_; 
v_key_2203_ = lean_ctor_get(v_entry_2202_, 0);
lean_inc(v_key_2203_);
lean_dec_ref(v_entry_2202_);
v___x_2204_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2195_, v_key_2203_);
lean_dec(v_key_2203_);
if (v___x_2204_ == 0)
{
lean_dec(v_j_2201_);
return v_x_2193_;
}
else
{
lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2212_; 
lean_inc_ref(v_es_2196_);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_x_2193_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v_x_2193_, 0);
lean_dec(v_unused_2213_);
v___x_2206_ = v_x_2193_;
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
else
{
lean_dec(v_x_2193_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2212_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_array_set(v_es_2196_, v_j_2201_, v___x_2197_);
lean_dec(v_j_2201_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2208_);
v___x_2210_ = v___x_2206_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
case 1:
{
lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2247_; 
lean_inc_ref(v_es_2196_);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_x_2193_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v_x_2193_, 0);
lean_dec(v_unused_2248_);
v___x_2215_ = v_x_2193_;
v_isShared_2216_ = v_isSharedCheck_2247_;
goto v_resetjp_2214_;
}
else
{
lean_dec(v_x_2193_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2247_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v_node_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2246_; 
v_node_2217_ = lean_ctor_get(v_entry_2202_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_entry_2202_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2219_ = v_entry_2202_;
v_isShared_2220_ = v_isSharedCheck_2246_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_node_2217_);
lean_dec(v_entry_2202_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2246_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v_entries_2221_; size_t v___x_2222_; lean_object* v_newNode_2223_; lean_object* v___x_2224_; 
v_entries_2221_ = lean_array_set(v_es_2196_, v_j_2201_, v___x_2197_);
v___x_2222_ = lean_usize_shift_right(v_x_2194_, v___x_2198_);
v_newNode_2223_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2217_, v___x_2222_, v_x_2195_);
lean_inc_ref(v_newNode_2223_);
v___x_2224_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2223_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v___x_2226_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v_newNode_2223_);
v___x_2226_ = v___x_2219_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_newNode_2223_);
v___x_2226_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = lean_array_set(v_entries_2221_, v_j_2201_, v___x_2226_);
lean_dec(v_j_2201_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2227_);
v___x_2229_ = v___x_2215_;
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
else
{
lean_object* v_val_2232_; lean_object* v_fst_2233_; lean_object* v_snd_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v_newNode_2223_);
lean_del_object(v___x_2219_);
v_val_2232_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_val_2232_);
lean_dec_ref(v___x_2224_);
v_fst_2233_ = lean_ctor_get(v_val_2232_, 0);
v_snd_2234_ = lean_ctor_get(v_val_2232_, 1);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_val_2232_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2236_ = v_val_2232_;
v_isShared_2237_ = v_isSharedCheck_2245_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_snd_2234_);
lean_inc(v_fst_2233_);
lean_dec(v_val_2232_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2245_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_fst_2233_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_snd_2234_);
v___x_2239_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = lean_array_set(v_entries_2221_, v_j_2201_, v___x_2239_);
lean_dec(v_j_2201_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2240_);
v___x_2242_ = v___x_2215_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2201_);
return v_x_2193_;
}
}
}
else
{
lean_object* v_ks_2249_; lean_object* v_vs_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2264_; 
v_ks_2249_ = lean_ctor_get(v_x_2193_, 0);
v_vs_2250_ = lean_ctor_get(v_x_2193_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_x_2193_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2252_ = v_x_2193_;
v_isShared_2253_ = v_isSharedCheck_2264_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_vs_2250_);
lean_inc(v_ks_2249_);
lean_dec(v_x_2193_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2264_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2249_, v_x_2195_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v___x_2256_; 
if (v_isShared_2253_ == 0)
{
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_ks_2249_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_vs_2250_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
else
{
lean_object* v_val_2258_; lean_object* v_keys_x27_2259_; lean_object* v_vals_x27_2260_; lean_object* v___x_2262_; 
v_val_2258_ = lean_ctor_get(v___x_2254_, 0);
lean_inc_n(v_val_2258_, 2);
lean_dec_ref(v___x_2254_);
v_keys_x27_2259_ = l_Array_eraseIdx___redArg(v_ks_2249_, v_val_2258_);
v_vals_x27_2260_ = l_Array_eraseIdx___redArg(v_vs_2250_, v_val_2258_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 1, v_vals_x27_2260_);
lean_ctor_set(v___x_2252_, 0, v_keys_x27_2259_);
v___x_2262_ = v___x_2252_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_keys_x27_2259_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_vals_x27_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_){
_start:
{
size_t v_x_21947__boxed_2268_; lean_object* v_res_2269_; 
v_x_21947__boxed_2268_ = lean_unbox_usize(v_x_2266_);
lean_dec(v_x_2266_);
v_res_2269_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2265_, v_x_21947__boxed_2268_, v_x_2267_);
lean_dec_ref(v_x_2267_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2270_, lean_object* v_x_2271_){
_start:
{
uint64_t v___x_2272_; size_t v_h_2273_; lean_object* v___x_2274_; 
v___x_2272_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2271_);
v_h_2273_ = lean_uint64_to_usize(v___x_2272_);
v___x_2274_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2270_, v_h_2273_, v_x_2271_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2275_, lean_object* v_x_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2275_, v_x_2276_);
lean_dec_ref(v_x_2276_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
if (lean_obj_tag(v_as_2278_) == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_box(0);
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
return v___x_2291_;
}
else
{
lean_object* v_head_2292_; lean_object* v_tail_2293_; lean_object* v___x_2294_; 
v_head_2292_ = lean_ctor_get(v_as_2278_, 0);
lean_inc(v_head_2292_);
v_tail_2293_ = lean_ctor_get(v_as_2278_, 1);
lean_inc(v_tail_2293_);
lean_dec_ref(v_as_2278_);
v___x_2294_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2292_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_dec_ref(v___x_2294_);
v_as_2278_ = v_tail_2293_;
goto _start;
}
else
{
lean_dec(v_tail_2293_);
return v___x_2294_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec(v___y_2297_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2309_, lean_object* v_vals_2310_, lean_object* v_i_2311_, lean_object* v_k_2312_){
_start:
{
lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = lean_array_get_size(v_keys_2309_);
v___x_2314_ = lean_nat_dec_lt(v_i_2311_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; 
lean_dec(v_i_2311_);
v___x_2315_ = lean_box(0);
return v___x_2315_;
}
else
{
lean_object* v_k_x27_2316_; uint8_t v___x_2317_; 
v_k_x27_2316_ = lean_array_fget_borrowed(v_keys_2309_, v_i_2311_);
v___x_2317_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_2312_, v_k_x27_2316_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_unsigned_to_nat(1u);
v___x_2319_ = lean_nat_add(v_i_2311_, v___x_2318_);
lean_dec(v_i_2311_);
v_i_2311_ = v___x_2319_;
goto _start;
}
else
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_array_fget_borrowed(v_vals_2310_, v_i_2311_);
lean_dec(v_i_2311_);
lean_inc(v___x_2321_);
v___x_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2323_, lean_object* v_vals_2324_, lean_object* v_i_2325_, lean_object* v_k_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2323_, v_vals_2324_, v_i_2325_, v_k_2326_);
lean_dec_ref(v_k_2326_);
lean_dec_ref(v_vals_2324_);
lean_dec_ref(v_keys_2323_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2328_, size_t v_x_2329_, lean_object* v_x_2330_){
_start:
{
if (lean_obj_tag(v_x_2328_) == 0)
{
lean_object* v_es_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2352_; 
v_es_2331_ = lean_ctor_get(v_x_2328_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_x_2328_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2333_ = v_x_2328_;
v_isShared_2334_ = v_isSharedCheck_2352_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_es_2331_);
lean_dec(v_x_2328_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2352_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; size_t v___x_2336_; size_t v___x_2337_; size_t v___x_2338_; lean_object* v_j_2339_; lean_object* v___x_2340_; 
v___x_2335_ = lean_box(2);
v___x_2336_ = ((size_t)5ULL);
v___x_2337_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2338_ = lean_usize_land(v_x_2329_, v___x_2337_);
v_j_2339_ = lean_usize_to_nat(v___x_2338_);
v___x_2340_ = lean_array_get(v___x_2335_, v_es_2331_, v_j_2339_);
lean_dec(v_j_2339_);
lean_dec_ref(v_es_2331_);
switch(lean_obj_tag(v___x_2340_))
{
case 0:
{
lean_object* v_key_2341_; lean_object* v_val_2342_; uint8_t v___x_2343_; 
v_key_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_key_2341_);
v_val_2342_ = lean_ctor_get(v___x_2340_, 1);
lean_inc(v_val_2342_);
lean_dec_ref(v___x_2340_);
v___x_2343_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2330_, v_key_2341_);
lean_dec(v_key_2341_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; 
lean_dec(v_val_2342_);
lean_del_object(v___x_2333_);
v___x_2344_ = lean_box(0);
return v___x_2344_;
}
else
{
lean_object* v___x_2346_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set_tag(v___x_2333_, 1);
lean_ctor_set(v___x_2333_, 0, v_val_2342_);
v___x_2346_ = v___x_2333_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_val_2342_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
case 1:
{
lean_object* v_node_2348_; size_t v___x_2349_; 
lean_del_object(v___x_2333_);
v_node_2348_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_node_2348_);
lean_dec_ref(v___x_2340_);
v___x_2349_ = lean_usize_shift_right(v_x_2329_, v___x_2336_);
v_x_2328_ = v_node_2348_;
v_x_2329_ = v___x_2349_;
goto _start;
}
default: 
{
lean_object* v___x_2351_; 
lean_del_object(v___x_2333_);
v___x_2351_ = lean_box(0);
return v___x_2351_;
}
}
}
}
else
{
lean_object* v_ks_2353_; lean_object* v_vs_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_ks_2353_ = lean_ctor_get(v_x_2328_, 0);
lean_inc_ref(v_ks_2353_);
v_vs_2354_ = lean_ctor_get(v_x_2328_, 1);
lean_inc_ref(v_vs_2354_);
lean_dec_ref(v_x_2328_);
v___x_2355_ = lean_unsigned_to_nat(0u);
v___x_2356_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2353_, v_vs_2354_, v___x_2355_, v_x_2330_);
lean_dec_ref(v_vs_2354_);
lean_dec_ref(v_ks_2353_);
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2357_, lean_object* v_x_2358_, lean_object* v_x_2359_){
_start:
{
size_t v_x_22166__boxed_2360_; lean_object* v_res_2361_; 
v_x_22166__boxed_2360_ = lean_unbox_usize(v_x_2358_);
lean_dec(v_x_2358_);
v_res_2361_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2357_, v_x_22166__boxed_2360_, v_x_2359_);
lean_dec_ref(v_x_2359_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2362_, lean_object* v_x_2363_){
_start:
{
uint64_t v___x_2364_; size_t v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2363_);
v___x_2365_ = lean_uint64_to_usize(v___x_2364_);
v___x_2366_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2362_, v___x_2365_, v_x_2363_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2367_, v_x_2368_);
lean_dec_ref(v_x_2368_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2370_, lean_object* v_b_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
if (lean_obj_tag(v_as_x27_2370_) == 0)
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_b_2371_);
return v___x_2383_;
}
else
{
lean_object* v_head_2384_; lean_object* v_tail_2385_; lean_object* v___x_2386_; lean_object* v_toGoalState_2387_; lean_object* v_ematch_2388_; lean_object* v_delayedThmInsts_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v_head_2384_ = lean_ctor_get(v_as_x27_2370_, 0);
v_tail_2385_ = lean_ctor_get(v_as_x27_2370_, 1);
v___x_2386_ = lean_st_ref_get(v___y_2372_);
v_toGoalState_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc_ref(v_toGoalState_2387_);
lean_dec(v___x_2386_);
v_ematch_2388_ = lean_ctor_get(v_toGoalState_2387_, 12);
lean_inc_ref(v_ematch_2388_);
lean_dec_ref(v_toGoalState_2387_);
v_delayedThmInsts_2389_ = lean_ctor_get(v_ematch_2388_, 10);
lean_inc_ref(v_delayedThmInsts_2389_);
lean_dec_ref(v_ematch_2388_);
v___x_2390_ = lean_box(0);
v___x_2391_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2389_, v_head_2384_);
if (lean_obj_tag(v___x_2391_) == 1)
{
lean_object* v_val_2392_; lean_object* v___x_2393_; lean_object* v_toGoalState_2394_; lean_object* v_ematch_2395_; lean_object* v_mvarId_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2450_; 
v_val_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_val_2392_);
lean_dec_ref(v___x_2391_);
v___x_2393_ = lean_st_ref_take(v___y_2372_);
v_toGoalState_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc_ref(v_toGoalState_2394_);
v_ematch_2395_ = lean_ctor_get(v_toGoalState_2394_, 12);
lean_inc_ref(v_ematch_2395_);
v_mvarId_2396_ = lean_ctor_get(v___x_2393_, 1);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; 
v_unused_2451_ = lean_ctor_get(v___x_2393_, 0);
lean_dec(v_unused_2451_);
v___x_2398_ = v___x_2393_;
v_isShared_2399_ = v_isSharedCheck_2450_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_mvarId_2396_);
lean_dec(v___x_2393_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2450_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_nextDeclIdx_2400_; lean_object* v_enodeMap_2401_; lean_object* v_exprs_2402_; lean_object* v_parents_2403_; lean_object* v_congrTable_2404_; lean_object* v_appMap_2405_; lean_object* v_indicesFound_2406_; lean_object* v_newFacts_2407_; uint8_t v_inconsistent_2408_; lean_object* v_nextIdx_2409_; lean_object* v_newRawFacts_2410_; lean_object* v_facts_2411_; lean_object* v_extThms_2412_; lean_object* v_inj_2413_; lean_object* v_split_2414_; lean_object* v_clean_2415_; lean_object* v_sstates_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2448_; 
v_nextDeclIdx_2400_ = lean_ctor_get(v_toGoalState_2394_, 0);
v_enodeMap_2401_ = lean_ctor_get(v_toGoalState_2394_, 1);
v_exprs_2402_ = lean_ctor_get(v_toGoalState_2394_, 2);
v_parents_2403_ = lean_ctor_get(v_toGoalState_2394_, 3);
v_congrTable_2404_ = lean_ctor_get(v_toGoalState_2394_, 4);
v_appMap_2405_ = lean_ctor_get(v_toGoalState_2394_, 5);
v_indicesFound_2406_ = lean_ctor_get(v_toGoalState_2394_, 6);
v_newFacts_2407_ = lean_ctor_get(v_toGoalState_2394_, 7);
v_inconsistent_2408_ = lean_ctor_get_uint8(v_toGoalState_2394_, sizeof(void*)*17);
v_nextIdx_2409_ = lean_ctor_get(v_toGoalState_2394_, 8);
v_newRawFacts_2410_ = lean_ctor_get(v_toGoalState_2394_, 9);
v_facts_2411_ = lean_ctor_get(v_toGoalState_2394_, 10);
v_extThms_2412_ = lean_ctor_get(v_toGoalState_2394_, 11);
v_inj_2413_ = lean_ctor_get(v_toGoalState_2394_, 13);
v_split_2414_ = lean_ctor_get(v_toGoalState_2394_, 14);
v_clean_2415_ = lean_ctor_get(v_toGoalState_2394_, 15);
v_sstates_2416_ = lean_ctor_get(v_toGoalState_2394_, 16);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_toGoalState_2394_);
if (v_isSharedCheck_2448_ == 0)
{
lean_object* v_unused_2449_; 
v_unused_2449_ = lean_ctor_get(v_toGoalState_2394_, 12);
lean_dec(v_unused_2449_);
v___x_2418_ = v_toGoalState_2394_;
v_isShared_2419_ = v_isSharedCheck_2448_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_sstates_2416_);
lean_inc(v_clean_2415_);
lean_inc(v_split_2414_);
lean_inc(v_inj_2413_);
lean_inc(v_extThms_2412_);
lean_inc(v_facts_2411_);
lean_inc(v_newRawFacts_2410_);
lean_inc(v_nextIdx_2409_);
lean_inc(v_newFacts_2407_);
lean_inc(v_indicesFound_2406_);
lean_inc(v_appMap_2405_);
lean_inc(v_congrTable_2404_);
lean_inc(v_parents_2403_);
lean_inc(v_exprs_2402_);
lean_inc(v_enodeMap_2401_);
lean_inc(v_nextDeclIdx_2400_);
lean_dec(v_toGoalState_2394_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2448_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_thmMap_2420_; lean_object* v_gmt_2421_; lean_object* v_thms_2422_; lean_object* v_newThms_2423_; lean_object* v_numInstances_2424_; lean_object* v_numDelayedInstances_2425_; lean_object* v_num_2426_; lean_object* v_preInstances_2427_; lean_object* v_nextThmIdx_2428_; lean_object* v_matchEqNames_2429_; lean_object* v_delayedThmInsts_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2447_; 
v_thmMap_2420_ = lean_ctor_get(v_ematch_2395_, 0);
v_gmt_2421_ = lean_ctor_get(v_ematch_2395_, 1);
v_thms_2422_ = lean_ctor_get(v_ematch_2395_, 2);
v_newThms_2423_ = lean_ctor_get(v_ematch_2395_, 3);
v_numInstances_2424_ = lean_ctor_get(v_ematch_2395_, 4);
v_numDelayedInstances_2425_ = lean_ctor_get(v_ematch_2395_, 5);
v_num_2426_ = lean_ctor_get(v_ematch_2395_, 6);
v_preInstances_2427_ = lean_ctor_get(v_ematch_2395_, 7);
v_nextThmIdx_2428_ = lean_ctor_get(v_ematch_2395_, 8);
v_matchEqNames_2429_ = lean_ctor_get(v_ematch_2395_, 9);
v_delayedThmInsts_2430_ = lean_ctor_get(v_ematch_2395_, 10);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_ematch_2395_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2432_ = v_ematch_2395_;
v_isShared_2433_ = v_isSharedCheck_2447_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_delayedThmInsts_2430_);
lean_inc(v_matchEqNames_2429_);
lean_inc(v_nextThmIdx_2428_);
lean_inc(v_preInstances_2427_);
lean_inc(v_num_2426_);
lean_inc(v_numDelayedInstances_2425_);
lean_inc(v_numInstances_2424_);
lean_inc(v_newThms_2423_);
lean_inc(v_thms_2422_);
lean_inc(v_gmt_2421_);
lean_inc(v_thmMap_2420_);
lean_dec(v_ematch_2395_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2447_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2434_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2430_, v_head_2384_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 10, v___x_2434_);
v___x_2436_ = v___x_2432_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_thmMap_2420_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_gmt_2421_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_thms_2422_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_newThms_2423_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v_numInstances_2424_);
lean_ctor_set(v_reuseFailAlloc_2446_, 5, v_numDelayedInstances_2425_);
lean_ctor_set(v_reuseFailAlloc_2446_, 6, v_num_2426_);
lean_ctor_set(v_reuseFailAlloc_2446_, 7, v_preInstances_2427_);
lean_ctor_set(v_reuseFailAlloc_2446_, 8, v_nextThmIdx_2428_);
lean_ctor_set(v_reuseFailAlloc_2446_, 9, v_matchEqNames_2429_);
lean_ctor_set(v_reuseFailAlloc_2446_, 10, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2438_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 12, v___x_2436_);
v___x_2438_ = v___x_2418_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_nextDeclIdx_2400_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_enodeMap_2401_);
lean_ctor_set(v_reuseFailAlloc_2445_, 2, v_exprs_2402_);
lean_ctor_set(v_reuseFailAlloc_2445_, 3, v_parents_2403_);
lean_ctor_set(v_reuseFailAlloc_2445_, 4, v_congrTable_2404_);
lean_ctor_set(v_reuseFailAlloc_2445_, 5, v_appMap_2405_);
lean_ctor_set(v_reuseFailAlloc_2445_, 6, v_indicesFound_2406_);
lean_ctor_set(v_reuseFailAlloc_2445_, 7, v_newFacts_2407_);
lean_ctor_set(v_reuseFailAlloc_2445_, 8, v_nextIdx_2409_);
lean_ctor_set(v_reuseFailAlloc_2445_, 9, v_newRawFacts_2410_);
lean_ctor_set(v_reuseFailAlloc_2445_, 10, v_facts_2411_);
lean_ctor_set(v_reuseFailAlloc_2445_, 11, v_extThms_2412_);
lean_ctor_set(v_reuseFailAlloc_2445_, 12, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2445_, 13, v_inj_2413_);
lean_ctor_set(v_reuseFailAlloc_2445_, 14, v_split_2414_);
lean_ctor_set(v_reuseFailAlloc_2445_, 15, v_clean_2415_);
lean_ctor_set(v_reuseFailAlloc_2445_, 16, v_sstates_2416_);
lean_ctor_set_uint8(v_reuseFailAlloc_2445_, sizeof(void*)*17, v_inconsistent_2408_);
v___x_2438_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2440_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2438_);
v___x_2440_ = v___x_2398_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_mvarId_2396_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_st_ref_set(v___y_2372_, v___x_2440_);
v___x_2442_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2392_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_dec_ref(v___x_2442_);
v_as_x27_2370_ = v_tail_2385_;
v_b_2371_ = v___x_2390_;
goto _start;
}
else
{
return v___x_2442_;
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
lean_dec(v___x_2391_);
v_as_x27_2370_ = v_tail_2385_;
v_b_2371_ = v___x_2390_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2453_, lean_object* v_b_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2453_, v_b_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec(v_as_x27_2453_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2468_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2508_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2508_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2508_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_unbox(v_a_2480_);
lean_dec(v_a_2480_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v_toGoalState_2486_; lean_object* v_ematch_2487_; lean_object* v_delayedThmInsts_2488_; uint8_t v___x_2489_; 
v___x_2485_ = lean_st_ref_get(v_a_2468_);
v_toGoalState_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc_ref(v_toGoalState_2486_);
lean_dec(v___x_2485_);
v_ematch_2487_ = lean_ctor_get(v_toGoalState_2486_, 12);
lean_inc_ref(v_ematch_2487_);
lean_dec_ref(v_toGoalState_2486_);
v_delayedThmInsts_2488_ = lean_ctor_get(v_ematch_2487_, 10);
lean_inc_ref(v_delayedThmInsts_2488_);
lean_dec_ref(v_ematch_2487_);
v___x_2489_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2488_);
lean_dec_ref(v_delayedThmInsts_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_del_object(v___x_2482_);
v___x_2490_ = lean_box(0);
v___x_2491_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2467_, v___x_2490_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; 
v_unused_2499_ = lean_ctor_get(v___x_2491_, 0);
lean_dec(v_unused_2499_);
v___x_2493_ = v___x_2491_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_dec(v___x_2491_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2490_);
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2490_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
else
{
return v___x_2491_;
}
}
else
{
lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2500_ = lean_box(0);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2500_);
v___x_2502_ = v___x_2482_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = lean_box(0);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2504_);
v___x_2506_ = v___x_2482_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_a_2509_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2479_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2479_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_, v_a_2527_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec(v_toPropagateDown_2517_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2530_, lean_object* v_x_2531_, lean_object* v_x_2532_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2531_, v_x_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2534_, lean_object* v_x_2535_, lean_object* v_x_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2534_, v_x_2535_, v_x_2536_);
lean_dec_ref(v_x_2536_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2538_, lean_object* v_x_2539_, lean_object* v_x_2540_){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2539_, v_x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2542_, lean_object* v_x_2543_, lean_object* v_x_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2542_, v_x_2543_, v_x_2544_);
lean_dec_ref(v_x_2544_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2546_, lean_object* v_as_x27_2547_, lean_object* v_b_2548_, lean_object* v_a_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2547_, v_b_2548_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2562_, lean_object* v_as_x27_2563_, lean_object* v_b_2564_, lean_object* v_a_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2562_, v_as_x27_2563_, v_b_2564_, v_a_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec(v_as_x27_2563_);
lean_dec(v_as_2562_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2578_, lean_object* v_x_2579_, size_t v_x_2580_, lean_object* v_x_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2579_, v_x_2580_, v_x_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2583_, lean_object* v_x_2584_, lean_object* v_x_2585_, lean_object* v_x_2586_){
_start:
{
size_t v_x_22475__boxed_2587_; lean_object* v_res_2588_; 
v_x_22475__boxed_2587_ = lean_unbox_usize(v_x_2585_);
lean_dec(v_x_2585_);
v_res_2588_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2583_, v_x_2584_, v_x_22475__boxed_2587_, v_x_2586_);
lean_dec_ref(v_x_2586_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2589_, lean_object* v_x_2590_, size_t v_x_2591_, lean_object* v_x_2592_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2590_, v_x_2591_, v_x_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2594_, lean_object* v_x_2595_, lean_object* v_x_2596_, lean_object* v_x_2597_){
_start:
{
size_t v_x_22486__boxed_2598_; lean_object* v_res_2599_; 
v_x_22486__boxed_2598_ = lean_unbox_usize(v_x_2596_);
lean_dec(v_x_2596_);
v_res_2599_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2594_, v_x_2595_, v_x_22486__boxed_2598_, v_x_2597_);
lean_dec_ref(v_x_2597_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2600_, lean_object* v_keys_2601_, lean_object* v_vals_2602_, lean_object* v_heq_2603_, lean_object* v_i_2604_, lean_object* v_k_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2601_, v_vals_2602_, v_i_2604_, v_k_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2607_, lean_object* v_keys_2608_, lean_object* v_vals_2609_, lean_object* v_heq_2610_, lean_object* v_i_2611_, lean_object* v_k_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2607_, v_keys_2608_, v_vals_2609_, v_heq_2610_, v_i_2611_, v_k_2612_);
lean_dec_ref(v_k_2612_);
lean_dec_ref(v_vals_2609_);
lean_dec_ref(v_keys_2608_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2614_, lean_object* v_keys_2615_, lean_object* v_vals_2616_, lean_object* v_i_2617_, lean_object* v_k_2618_){
_start:
{
lean_object* v___x_2619_; uint8_t v___x_2620_; 
v___x_2619_ = lean_array_get_size(v_keys_2615_);
v___x_2620_ = lean_nat_dec_lt(v_i_2617_, v___x_2619_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; 
lean_dec_ref(v_k_2618_);
lean_dec(v_i_2617_);
lean_dec_ref(v___x_2614_);
v___x_2621_ = lean_box(0);
return v___x_2621_;
}
else
{
lean_object* v_k_x27_2622_; uint8_t v___x_2623_; 
v_k_x27_2622_ = lean_array_fget_borrowed(v_keys_2615_, v_i_2617_);
lean_inc(v_k_x27_2622_);
lean_inc_ref(v_k_2618_);
lean_inc_ref(v___x_2614_);
v___x_2623_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2614_, v_k_2618_, v_k_x27_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_unsigned_to_nat(1u);
v___x_2625_ = lean_nat_add(v_i_2617_, v___x_2624_);
lean_dec(v_i_2617_);
v_i_2617_ = v___x_2625_;
goto _start;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_dec_ref(v_k_2618_);
lean_dec_ref(v___x_2614_);
v___x_2627_ = lean_array_fget_borrowed(v_vals_2616_, v_i_2617_);
lean_dec(v_i_2617_);
lean_inc(v___x_2627_);
lean_inc(v_k_x27_2622_);
v___x_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2628_, 0, v_k_x27_2622_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
return v___x_2629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2630_, lean_object* v_keys_2631_, lean_object* v_vals_2632_, lean_object* v_i_2633_, lean_object* v_k_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2630_, v_keys_2631_, v_vals_2632_, v_i_2633_, v_k_2634_);
lean_dec_ref(v_vals_2632_);
lean_dec_ref(v_keys_2631_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2636_, lean_object* v_x_2637_, size_t v_x_2638_, lean_object* v_x_2639_){
_start:
{
if (lean_obj_tag(v_x_2637_) == 0)
{
lean_object* v_es_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2668_; 
v_es_2640_ = lean_ctor_get(v_x_2637_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_x_2637_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2642_ = v_x_2637_;
v_isShared_2643_ = v_isSharedCheck_2668_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_es_2640_);
lean_dec(v_x_2637_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2668_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; size_t v___x_2645_; size_t v___x_2646_; size_t v___x_2647_; lean_object* v_j_2648_; lean_object* v___x_2649_; 
v___x_2644_ = lean_box(2);
v___x_2645_ = ((size_t)5ULL);
v___x_2646_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2647_ = lean_usize_land(v_x_2638_, v___x_2646_);
v_j_2648_ = lean_usize_to_nat(v___x_2647_);
v___x_2649_ = lean_array_get(v___x_2644_, v_es_2640_, v_j_2648_);
lean_dec(v_j_2648_);
lean_dec_ref(v_es_2640_);
switch(lean_obj_tag(v___x_2649_))
{
case 0:
{
lean_object* v_key_2650_; lean_object* v_val_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2663_; 
v_key_2650_ = lean_ctor_get(v___x_2649_, 0);
v_val_2651_ = lean_ctor_get(v___x_2649_, 1);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2653_ = v___x_2649_;
v_isShared_2654_ = v_isSharedCheck_2663_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_val_2651_);
lean_inc(v_key_2650_);
lean_dec(v___x_2649_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2663_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
uint8_t v___x_2655_; 
lean_inc(v_key_2650_);
v___x_2655_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2636_, v_x_2639_, v_key_2650_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
lean_del_object(v___x_2653_);
lean_dec(v_val_2651_);
lean_dec(v_key_2650_);
lean_del_object(v___x_2642_);
v___x_2656_ = lean_box(0);
return v___x_2656_;
}
else
{
lean_object* v___x_2658_; 
if (v_isShared_2654_ == 0)
{
v___x_2658_ = v___x_2653_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_key_2650_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v_val_2651_);
v___x_2658_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2660_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set_tag(v___x_2642_, 1);
lean_ctor_set(v___x_2642_, 0, v___x_2658_);
v___x_2660_ = v___x_2642_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
}
case 1:
{
lean_object* v_node_2664_; size_t v___x_2665_; 
lean_del_object(v___x_2642_);
v_node_2664_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_node_2664_);
lean_dec_ref(v___x_2649_);
v___x_2665_ = lean_usize_shift_right(v_x_2638_, v___x_2645_);
v_x_2637_ = v_node_2664_;
v_x_2638_ = v___x_2665_;
goto _start;
}
default: 
{
lean_object* v___x_2667_; 
lean_del_object(v___x_2642_);
lean_dec_ref(v_x_2639_);
lean_dec_ref(v___x_2636_);
v___x_2667_ = lean_box(0);
return v___x_2667_;
}
}
}
}
else
{
lean_object* v_ks_2669_; lean_object* v_vs_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_ks_2669_ = lean_ctor_get(v_x_2637_, 0);
lean_inc_ref(v_ks_2669_);
v_vs_2670_ = lean_ctor_get(v_x_2637_, 1);
lean_inc_ref(v_vs_2670_);
lean_dec_ref(v_x_2637_);
v___x_2671_ = lean_unsigned_to_nat(0u);
v___x_2672_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2636_, v_ks_2669_, v_vs_2670_, v___x_2671_, v_x_2639_);
lean_dec_ref(v_vs_2670_);
lean_dec_ref(v_ks_2669_);
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_){
_start:
{
size_t v_x_27410__boxed_2677_; lean_object* v_res_2678_; 
v_x_27410__boxed_2677_ = lean_unbox_usize(v_x_2675_);
lean_dec(v_x_2675_);
v_res_2678_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2673_, v_x_2674_, v_x_27410__boxed_2677_, v_x_2676_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2679_, lean_object* v_x_2680_, lean_object* v_x_2681_){
_start:
{
uint64_t v___x_2682_; size_t v___x_2683_; lean_object* v___x_2684_; 
lean_inc_ref(v_x_2681_);
lean_inc_ref(v___x_2679_);
v___x_2682_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2679_, v_x_2681_);
v___x_2683_ = lean_uint64_to_usize(v___x_2682_);
v___x_2684_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2679_, v_x_2680_, v___x_2683_, v_x_2681_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2685_, lean_object* v_x_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_){
_start:
{
lean_object* v_ks_2690_; lean_object* v_vs_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2715_; 
v_ks_2690_ = lean_ctor_get(v_x_2686_, 0);
v_vs_2691_ = lean_ctor_get(v_x_2686_, 1);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_x_2686_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2693_ = v_x_2686_;
v_isShared_2694_ = v_isSharedCheck_2715_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_vs_2691_);
lean_inc(v_ks_2690_);
lean_dec(v_x_2686_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2715_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = lean_array_get_size(v_ks_2690_);
v___x_2696_ = lean_nat_dec_lt(v_x_2687_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
lean_dec(v_x_2687_);
lean_dec_ref(v___x_2685_);
v___x_2697_ = lean_array_push(v_ks_2690_, v_x_2688_);
v___x_2698_ = lean_array_push(v_vs_2691_, v_x_2689_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v___x_2698_);
lean_ctor_set(v___x_2693_, 0, v___x_2697_);
v___x_2700_ = v___x_2693_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
else
{
lean_object* v_k_x27_2702_; uint8_t v___x_2703_; 
v_k_x27_2702_ = lean_array_fget_borrowed(v_ks_2690_, v_x_2687_);
lean_inc(v_k_x27_2702_);
lean_inc_ref(v_x_2688_);
lean_inc_ref(v___x_2685_);
v___x_2703_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2685_, v_x_2688_, v_k_x27_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2705_; 
if (v_isShared_2694_ == 0)
{
v___x_2705_ = v___x_2693_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_ks_2690_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_vs_2691_);
v___x_2705_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_unsigned_to_nat(1u);
v___x_2707_ = lean_nat_add(v_x_2687_, v___x_2706_);
lean_dec(v_x_2687_);
v_x_2686_ = v___x_2705_;
v_x_2687_ = v___x_2707_;
goto _start;
}
}
else
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; 
lean_dec_ref(v___x_2685_);
v___x_2710_ = lean_array_fset(v_ks_2690_, v_x_2687_, v_x_2688_);
v___x_2711_ = lean_array_fset(v_vs_2691_, v_x_2687_, v_x_2689_);
lean_dec(v_x_2687_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v___x_2711_);
lean_ctor_set(v___x_2693_, 0, v___x_2710_);
v___x_2713_ = v___x_2693_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2716_, lean_object* v_n_2717_, lean_object* v_k_2718_, lean_object* v_v_2719_){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2716_, v_n_2717_, v___x_2720_, v_k_2718_, v_v_2719_);
return v___x_2721_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2723_, lean_object* v_x_2724_, size_t v_x_2725_, size_t v_x_2726_, lean_object* v_x_2727_, lean_object* v_x_2728_){
_start:
{
if (lean_obj_tag(v_x_2724_) == 0)
{
lean_object* v_es_2729_; size_t v___x_2730_; size_t v___x_2731_; size_t v___x_2732_; size_t v___x_2733_; lean_object* v_j_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v_es_2729_ = lean_ctor_get(v_x_2724_, 0);
v___x_2730_ = ((size_t)5ULL);
v___x_2731_ = ((size_t)1ULL);
v___x_2732_ = lean_usize_once(&l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___closed__1);
v___x_2733_ = lean_usize_land(v_x_2725_, v___x_2732_);
v_j_2734_ = lean_usize_to_nat(v___x_2733_);
v___x_2735_ = lean_array_get_size(v_es_2729_);
v___x_2736_ = lean_nat_dec_lt(v_j_2734_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_dec(v_j_2734_);
lean_dec(v_x_2728_);
lean_dec_ref(v_x_2727_);
lean_dec_ref(v___x_2723_);
return v_x_2724_;
}
else
{
lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2773_; 
lean_inc_ref(v_es_2729_);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_x_2724_);
if (v_isSharedCheck_2773_ == 0)
{
lean_object* v_unused_2774_; 
v_unused_2774_ = lean_ctor_get(v_x_2724_, 0);
lean_dec(v_unused_2774_);
v___x_2738_ = v_x_2724_;
v_isShared_2739_ = v_isSharedCheck_2773_;
goto v_resetjp_2737_;
}
else
{
lean_dec(v_x_2724_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2773_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v_v_2740_; lean_object* v___x_2741_; lean_object* v_xs_x27_2742_; lean_object* v___y_2744_; 
v_v_2740_ = lean_array_fget(v_es_2729_, v_j_2734_);
v___x_2741_ = lean_box(0);
v_xs_x27_2742_ = lean_array_fset(v_es_2729_, v_j_2734_, v___x_2741_);
switch(lean_obj_tag(v_v_2740_))
{
case 0:
{
lean_object* v_key_2749_; lean_object* v_val_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2760_; 
v_key_2749_ = lean_ctor_get(v_v_2740_, 0);
v_val_2750_ = lean_ctor_get(v_v_2740_, 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_v_2740_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2752_ = v_v_2740_;
v_isShared_2753_ = v_isSharedCheck_2760_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_val_2750_);
lean_inc(v_key_2749_);
lean_dec(v_v_2740_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2760_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
uint8_t v___x_2754_; 
lean_inc(v_key_2749_);
lean_inc_ref(v_x_2727_);
v___x_2754_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2723_, v_x_2727_, v_key_2749_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_del_object(v___x_2752_);
v___x_2755_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2749_, v_val_2750_, v_x_2727_, v_x_2728_);
v___x_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
v___y_2744_ = v___x_2756_;
goto v___jp_2743_;
}
else
{
lean_object* v___x_2758_; 
lean_dec(v_val_2750_);
lean_dec(v_key_2749_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 1, v_x_2728_);
lean_ctor_set(v___x_2752_, 0, v_x_2727_);
v___x_2758_ = v___x_2752_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_x_2727_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_x_2728_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
v___y_2744_ = v___x_2758_;
goto v___jp_2743_;
}
}
}
}
case 1:
{
lean_object* v_node_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2771_; 
v_node_2761_ = lean_ctor_get(v_v_2740_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_v_2740_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2763_ = v_v_2740_;
v_isShared_2764_ = v_isSharedCheck_2771_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_node_2761_);
lean_dec(v_v_2740_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2771_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
size_t v___x_2765_; size_t v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
v___x_2765_ = lean_usize_shift_right(v_x_2725_, v___x_2730_);
v___x_2766_ = lean_usize_add(v_x_2726_, v___x_2731_);
v___x_2767_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2723_, v_node_2761_, v___x_2765_, v___x_2766_, v_x_2727_, v_x_2728_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2767_);
v___x_2769_ = v___x_2763_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
v___y_2744_ = v___x_2769_;
goto v___jp_2743_;
}
}
}
default: 
{
lean_object* v___x_2772_; 
lean_dec_ref(v___x_2723_);
v___x_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2772_, 0, v_x_2727_);
lean_ctor_set(v___x_2772_, 1, v_x_2728_);
v___y_2744_ = v___x_2772_;
goto v___jp_2743_;
}
}
v___jp_2743_:
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2745_ = lean_array_fset(v_xs_x27_2742_, v_j_2734_, v___y_2744_);
lean_dec(v_j_2734_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2745_);
v___x_2747_ = v___x_2738_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
else
{
lean_object* v_ks_2775_; lean_object* v_vs_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2796_; 
v_ks_2775_ = lean_ctor_get(v_x_2724_, 0);
v_vs_2776_ = lean_ctor_get(v_x_2724_, 1);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_x_2724_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2778_ = v_x_2724_;
v_isShared_2779_ = v_isSharedCheck_2796_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_vs_2776_);
lean_inc(v_ks_2775_);
lean_dec(v_x_2724_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2796_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_ks_2775_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_vs_2776_);
v___x_2781_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v_newNode_2782_; uint8_t v___y_2784_; size_t v___x_2790_; uint8_t v___x_2791_; 
lean_inc_ref(v___x_2723_);
v_newNode_2782_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2723_, v___x_2781_, v_x_2727_, v_x_2728_);
v___x_2790_ = ((size_t)7ULL);
v___x_2791_ = lean_usize_dec_le(v___x_2790_, v_x_2726_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2792_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2782_);
v___x_2793_ = lean_unsigned_to_nat(4u);
v___x_2794_ = lean_nat_dec_lt(v___x_2792_, v___x_2793_);
lean_dec(v___x_2792_);
v___y_2784_ = v___x_2794_;
goto v___jp_2783_;
}
else
{
v___y_2784_ = v___x_2791_;
goto v___jp_2783_;
}
v___jp_2783_:
{
if (v___y_2784_ == 0)
{
lean_object* v_ks_2785_; lean_object* v_vs_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_ks_2785_ = lean_ctor_get(v_newNode_2782_, 0);
lean_inc_ref(v_ks_2785_);
v_vs_2786_ = lean_ctor_get(v_newNode_2782_, 1);
lean_inc_ref(v_vs_2786_);
lean_dec_ref(v_newNode_2782_);
v___x_2787_ = lean_unsigned_to_nat(0u);
v___x_2788_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2789_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2723_, v_x_2726_, v_ks_2785_, v_vs_2786_, v___x_2787_, v___x_2788_);
lean_dec_ref(v_vs_2786_);
lean_dec_ref(v_ks_2785_);
return v___x_2789_;
}
else
{
lean_dec_ref(v___x_2723_);
return v_newNode_2782_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2797_, size_t v_depth_2798_, lean_object* v_keys_2799_, lean_object* v_vals_2800_, lean_object* v_i_2801_, lean_object* v_entries_2802_){
_start:
{
lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2803_ = lean_array_get_size(v_keys_2799_);
v___x_2804_ = lean_nat_dec_lt(v_i_2801_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_dec(v_i_2801_);
lean_dec_ref(v___x_2797_);
return v_entries_2802_;
}
else
{
lean_object* v_k_2805_; lean_object* v_v_2806_; uint64_t v___x_2807_; size_t v_h_2808_; size_t v___x_2809_; lean_object* v___x_2810_; size_t v___x_2811_; size_t v___x_2812_; size_t v___x_2813_; size_t v_h_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_k_2805_ = lean_array_fget_borrowed(v_keys_2799_, v_i_2801_);
v_v_2806_ = lean_array_fget_borrowed(v_vals_2800_, v_i_2801_);
lean_inc_n(v_k_2805_, 2);
lean_inc_ref_n(v___x_2797_, 2);
v___x_2807_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2797_, v_k_2805_);
v_h_2808_ = lean_uint64_to_usize(v___x_2807_);
v___x_2809_ = ((size_t)5ULL);
v___x_2810_ = lean_unsigned_to_nat(1u);
v___x_2811_ = ((size_t)1ULL);
v___x_2812_ = lean_usize_sub(v_depth_2798_, v___x_2811_);
v___x_2813_ = lean_usize_mul(v___x_2809_, v___x_2812_);
v_h_2814_ = lean_usize_shift_right(v_h_2808_, v___x_2813_);
v___x_2815_ = lean_nat_add(v_i_2801_, v___x_2810_);
lean_dec(v_i_2801_);
lean_inc(v_v_2806_);
v___x_2816_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2797_, v_entries_2802_, v_h_2814_, v_depth_2798_, v_k_2805_, v_v_2806_);
v_i_2801_ = v___x_2815_;
v_entries_2802_ = v___x_2816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2818_, lean_object* v_depth_2819_, lean_object* v_keys_2820_, lean_object* v_vals_2821_, lean_object* v_i_2822_, lean_object* v_entries_2823_){
_start:
{
size_t v_depth_boxed_2824_; lean_object* v_res_2825_; 
v_depth_boxed_2824_ = lean_unbox_usize(v_depth_2819_);
lean_dec(v_depth_2819_);
v_res_2825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2818_, v_depth_boxed_2824_, v_keys_2820_, v_vals_2821_, v_i_2822_, v_entries_2823_);
lean_dec_ref(v_vals_2821_);
lean_dec_ref(v_keys_2820_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2826_, lean_object* v_x_2827_, lean_object* v_x_2828_, lean_object* v_x_2829_, lean_object* v_x_2830_, lean_object* v_x_2831_){
_start:
{
size_t v_x_27587__boxed_2832_; size_t v_x_27588__boxed_2833_; lean_object* v_res_2834_; 
v_x_27587__boxed_2832_ = lean_unbox_usize(v_x_2828_);
lean_dec(v_x_2828_);
v_x_27588__boxed_2833_ = lean_unbox_usize(v_x_2829_);
lean_dec(v_x_2829_);
v_res_2834_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2826_, v_x_2827_, v_x_27587__boxed_2832_, v_x_27588__boxed_2833_, v_x_2830_, v_x_2831_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2835_, lean_object* v_x_2836_, lean_object* v_x_2837_, lean_object* v_x_2838_){
_start:
{
uint64_t v___x_2839_; size_t v___x_2840_; size_t v___x_2841_; lean_object* v___x_2842_; 
lean_inc_ref(v_x_2837_);
lean_inc_ref(v___x_2835_);
v___x_2839_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2835_, v_x_2837_);
v___x_2840_ = lean_uint64_to_usize(v___x_2839_);
v___x_2841_ = ((size_t)1ULL);
v___x_2842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2835_, v_x_2836_, v___x_2840_, v___x_2841_, v_x_2837_, v_x_2838_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2847_, lean_object* v_rootNew_2848_, uint8_t v_a_2849_, lean_object* v_b_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v___x_2858_; lean_object* v_snd_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_3024_; 
v___x_2858_ = lean_st_ref_get(v___y_2851_);
v_snd_2859_ = lean_ctor_get(v_b_2850_, 1);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_b_2850_);
if (v_isSharedCheck_3024_ == 0)
{
lean_object* v_unused_3025_; 
v_unused_3025_ = lean_ctor_get(v_b_2850_, 0);
lean_dec(v_unused_3025_);
v___x_2861_ = v_b_2850_;
v_isShared_2862_ = v_isSharedCheck_3024_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_snd_2859_);
lean_dec(v_b_2850_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_3024_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; 
lean_inc(v_snd_2859_);
v___x_2863_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2858_, v_snd_2859_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_3015_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_3015_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_3015_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v_self_2868_; lean_object* v_next_2869_; lean_object* v_congr_2870_; lean_object* v_target_x3f_2871_; lean_object* v_proof_x3f_2872_; uint8_t v_flipped_2873_; lean_object* v_size_2874_; uint8_t v_interpreted_2875_; uint8_t v_ctor_2876_; uint8_t v_hasLambdas_2877_; uint8_t v_heqProofs_2878_; lean_object* v_idx_2879_; lean_object* v_generation_2880_; lean_object* v_mt_2881_; lean_object* v_sTerms_2882_; uint8_t v_funCC_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_3013_; 
v_self_2868_ = lean_ctor_get(v_a_2864_, 0);
v_next_2869_ = lean_ctor_get(v_a_2864_, 1);
v_congr_2870_ = lean_ctor_get(v_a_2864_, 3);
v_target_x3f_2871_ = lean_ctor_get(v_a_2864_, 4);
v_proof_x3f_2872_ = lean_ctor_get(v_a_2864_, 5);
v_flipped_2873_ = lean_ctor_get_uint8(v_a_2864_, sizeof(void*)*11);
v_size_2874_ = lean_ctor_get(v_a_2864_, 6);
v_interpreted_2875_ = lean_ctor_get_uint8(v_a_2864_, sizeof(void*)*11 + 1);
v_ctor_2876_ = lean_ctor_get_uint8(v_a_2864_, sizeof(void*)*11 + 2);
v_hasLambdas_2877_ = lean_ctor_get_uint8(v_a_2864_, sizeof(void*)*11 + 3);
v_heqProofs_2878_ = lean_ctor_get_uint8(v_a_2864_, sizeof(void*)*11 + 4);
v_idx_2879_ = lean_ctor_get(v_a_2864_, 7);
v_generation_2880_ = lean_ctor_get(v_a_2864_, 8);
v_mt_2881_ = lean_ctor_get(v_a_2864_, 9);
v_sTerms_2882_ = lean_ctor_get(v_a_2864_, 10);
v_funCC_2883_ = lean_ctor_get_uint8(v_a_2864_, sizeof(void*)*11 + 5);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_a_2864_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; 
v_unused_3014_ = lean_ctor_get(v_a_2864_, 2);
lean_dec(v_unused_3014_);
v___x_2885_ = v_a_2864_;
v_isShared_2886_ = v_isSharedCheck_3013_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_sTerms_2882_);
lean_inc(v_mt_2881_);
lean_inc(v_generation_2880_);
lean_inc(v_idx_2879_);
lean_inc(v_size_2874_);
lean_inc(v_proof_x3f_2872_);
lean_inc(v_target_x3f_2871_);
lean_inc(v_congr_2870_);
lean_inc(v_next_2869_);
lean_inc(v_self_2868_);
lean_dec(v_a_2864_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_3013_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___y_2902_; lean_object* v___x_2912_; 
v___x_2887_ = lean_box(0);
lean_inc(v_sTerms_2882_);
lean_inc(v_mt_2881_);
lean_inc(v_generation_2880_);
lean_inc(v_idx_2879_);
lean_inc(v_size_2874_);
lean_inc(v_proof_x3f_2872_);
lean_inc(v_target_x3f_2871_);
lean_inc_ref(v_rootNew_2848_);
lean_inc_ref(v_next_2869_);
lean_inc_ref(v_self_2868_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 2, v_rootNew_2848_);
v___x_2912_ = v___x_2885_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_self_2868_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_next_2869_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_rootNew_2848_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_congr_2870_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v_target_x3f_2871_);
lean_ctor_set(v_reuseFailAlloc_3012_, 5, v_proof_x3f_2872_);
lean_ctor_set(v_reuseFailAlloc_3012_, 6, v_size_2874_);
lean_ctor_set(v_reuseFailAlloc_3012_, 7, v_idx_2879_);
lean_ctor_set(v_reuseFailAlloc_3012_, 8, v_generation_2880_);
lean_ctor_set(v_reuseFailAlloc_3012_, 9, v_mt_2881_);
lean_ctor_set(v_reuseFailAlloc_3012_, 10, v_sTerms_2882_);
lean_ctor_set_uint8(v_reuseFailAlloc_3012_, sizeof(void*)*11, v_flipped_2873_);
lean_ctor_set_uint8(v_reuseFailAlloc_3012_, sizeof(void*)*11 + 1, v_interpreted_2875_);
lean_ctor_set_uint8(v_reuseFailAlloc_3012_, sizeof(void*)*11 + 2, v_ctor_2876_);
lean_ctor_set_uint8(v_reuseFailAlloc_3012_, sizeof(void*)*11 + 3, v_hasLambdas_2877_);
lean_ctor_set_uint8(v_reuseFailAlloc_3012_, sizeof(void*)*11 + 4, v_heqProofs_2878_);
lean_ctor_set_uint8(v_reuseFailAlloc_3012_, sizeof(void*)*11 + 5, v_funCC_2883_);
v___x_2912_ = v_reuseFailAlloc_3012_;
goto v_reusejp_2911_;
}
v___jp_2888_:
{
uint8_t v___x_2889_; 
v___x_2889_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_2869_, v_lhs_2847_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2891_; 
lean_del_object(v___x_2866_);
lean_dec(v_snd_2859_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 1, v_next_2869_);
lean_ctor_set(v___x_2861_, 0, v___x_2887_);
v___x_2891_ = v___x_2861_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_next_2869_);
v___x_2891_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
v_b_2850_ = v___x_2891_;
goto _start;
}
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_dec_ref(v_next_2869_);
lean_dec_ref(v_rootNew_2848_);
v___x_2894_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2894_);
v___x_2896_ = v___x_2861_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_snd_2859_);
v___x_2896_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2898_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v___x_2896_);
v___x_2898_ = v___x_2866_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
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
v___jp_2901_:
{
if (lean_obj_tag(v___y_2902_) == 0)
{
lean_dec_ref(v___y_2902_);
goto v___jp_2888_;
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec_ref(v_next_2869_);
lean_del_object(v___x_2866_);
lean_del_object(v___x_2861_);
lean_dec(v_snd_2859_);
lean_dec_ref(v_rootNew_2848_);
v_a_2903_ = lean_ctor_get(v___y_2902_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___y_2902_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___y_2902_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___y_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; 
lean_inc_ref(v___x_2912_);
lean_inc_ref(v_self_2868_);
v___x_2913_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2868_, v___x_2912_, v___y_2851_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_dec_ref(v___x_2913_);
if (v_a_2849_ == 0)
{
lean_dec_ref(v___x_2912_);
lean_dec(v_sTerms_2882_);
lean_dec(v_mt_2881_);
lean_dec(v_generation_2880_);
lean_dec(v_idx_2879_);
lean_dec(v_size_2874_);
lean_dec(v_proof_x3f_2872_);
lean_dec(v_target_x3f_2871_);
lean_dec_ref(v_self_2868_);
goto v___jp_2888_;
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v___x_2914_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2915_ = lean_unsigned_to_nat(3u);
v___x_2916_ = l_Lean_Expr_isAppOfArity(v_self_2868_, v___x_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_dec_ref(v___x_2912_);
lean_dec(v_sTerms_2882_);
lean_dec(v_mt_2881_);
lean_dec(v_generation_2880_);
lean_dec(v_idx_2879_);
lean_dec(v_size_2874_);
lean_dec(v_proof_x3f_2872_);
lean_dec(v_target_x3f_2871_);
lean_dec_ref(v_self_2868_);
goto v___jp_2888_;
}
else
{
uint8_t v___x_2917_; 
v___x_2917_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2912_);
lean_dec_ref(v___x_2912_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v_toGoalState_2919_; lean_object* v_enodeMap_2920_; lean_object* v_congrTable_2921_; lean_object* v___x_2922_; 
v___x_2918_ = lean_st_ref_get(v___y_2851_);
v_toGoalState_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc_ref(v_toGoalState_2919_);
lean_dec(v___x_2918_);
v_enodeMap_2920_ = lean_ctor_get(v_toGoalState_2919_, 1);
lean_inc_ref(v_enodeMap_2920_);
v_congrTable_2921_ = lean_ctor_get(v_toGoalState_2919_, 4);
lean_inc_ref(v_congrTable_2921_);
lean_dec_ref(v_toGoalState_2919_);
lean_inc_ref(v_self_2868_);
v___x_2922_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_2920_, v_congrTable_2921_, v_self_2868_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_dec(v_sTerms_2882_);
lean_dec(v_mt_2881_);
lean_dec(v_generation_2880_);
lean_dec(v_idx_2879_);
lean_dec(v_size_2874_);
lean_dec(v_proof_x3f_2872_);
lean_dec(v_target_x3f_2871_);
lean_dec_ref(v_self_2868_);
goto v___jp_2888_;
}
else
{
lean_object* v_val_2923_; lean_object* v_fst_2924_; lean_object* v___x_2925_; 
v_val_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_val_2923_);
lean_dec_ref(v___x_2922_);
v_fst_2924_ = lean_ctor_get(v_val_2923_, 0);
lean_inc(v_fst_2924_);
lean_dec(v_val_2923_);
v___x_2925_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_2924_, v___y_2852_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; uint8_t v___x_2927_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref(v___x_2925_);
v___x_2927_ = lean_unbox(v_a_2926_);
lean_dec(v_a_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; lean_object* v_toGoalState_2929_; lean_object* v_mvarId_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_3003_; 
v___x_2928_ = lean_st_ref_take(v___y_2851_);
v_toGoalState_2929_ = lean_ctor_get(v___x_2928_, 0);
v_mvarId_2930_ = lean_ctor_get(v___x_2928_, 1);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2932_ = v___x_2928_;
v_isShared_2933_ = v_isSharedCheck_3003_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_mvarId_2930_);
lean_inc(v_toGoalState_2929_);
lean_dec(v___x_2928_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_3003_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v_nextDeclIdx_2934_; lean_object* v_enodeMap_2935_; lean_object* v_exprs_2936_; lean_object* v_parents_2937_; lean_object* v_congrTable_2938_; lean_object* v_appMap_2939_; lean_object* v_indicesFound_2940_; lean_object* v_newFacts_2941_; uint8_t v_inconsistent_2942_; lean_object* v_nextIdx_2943_; lean_object* v_newRawFacts_2944_; lean_object* v_facts_2945_; lean_object* v_extThms_2946_; lean_object* v_ematch_2947_; lean_object* v_inj_2948_; lean_object* v_split_2949_; lean_object* v_clean_2950_; lean_object* v_sstates_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3002_; 
v_nextDeclIdx_2934_ = lean_ctor_get(v_toGoalState_2929_, 0);
v_enodeMap_2935_ = lean_ctor_get(v_toGoalState_2929_, 1);
v_exprs_2936_ = lean_ctor_get(v_toGoalState_2929_, 2);
v_parents_2937_ = lean_ctor_get(v_toGoalState_2929_, 3);
v_congrTable_2938_ = lean_ctor_get(v_toGoalState_2929_, 4);
v_appMap_2939_ = lean_ctor_get(v_toGoalState_2929_, 5);
v_indicesFound_2940_ = lean_ctor_get(v_toGoalState_2929_, 6);
v_newFacts_2941_ = lean_ctor_get(v_toGoalState_2929_, 7);
v_inconsistent_2942_ = lean_ctor_get_uint8(v_toGoalState_2929_, sizeof(void*)*17);
v_nextIdx_2943_ = lean_ctor_get(v_toGoalState_2929_, 8);
v_newRawFacts_2944_ = lean_ctor_get(v_toGoalState_2929_, 9);
v_facts_2945_ = lean_ctor_get(v_toGoalState_2929_, 10);
v_extThms_2946_ = lean_ctor_get(v_toGoalState_2929_, 11);
v_ematch_2947_ = lean_ctor_get(v_toGoalState_2929_, 12);
v_inj_2948_ = lean_ctor_get(v_toGoalState_2929_, 13);
v_split_2949_ = lean_ctor_get(v_toGoalState_2929_, 14);
v_clean_2950_ = lean_ctor_get(v_toGoalState_2929_, 15);
v_sstates_2951_ = lean_ctor_get(v_toGoalState_2929_, 16);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_toGoalState_2929_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2953_ = v_toGoalState_2929_;
v_isShared_2954_ = v_isSharedCheck_3002_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_sstates_2951_);
lean_inc(v_clean_2950_);
lean_inc(v_split_2949_);
lean_inc(v_inj_2948_);
lean_inc(v_ematch_2947_);
lean_inc(v_extThms_2946_);
lean_inc(v_facts_2945_);
lean_inc(v_newRawFacts_2944_);
lean_inc(v_nextIdx_2943_);
lean_inc(v_newFacts_2941_);
lean_inc(v_indicesFound_2940_);
lean_inc(v_appMap_2939_);
lean_inc(v_congrTable_2938_);
lean_inc(v_parents_2937_);
lean_inc(v_exprs_2936_);
lean_inc(v_enodeMap_2935_);
lean_inc(v_nextDeclIdx_2934_);
lean_dec(v_toGoalState_2929_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3002_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2955_ = lean_box(0);
lean_inc_ref(v_self_2868_);
lean_inc_ref(v_enodeMap_2935_);
v___x_2956_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_2935_, v_congrTable_2938_, v_self_2868_, v___x_2955_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 4, v___x_2956_);
v___x_2958_ = v___x_2953_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_nextDeclIdx_2934_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_enodeMap_2935_);
lean_ctor_set(v_reuseFailAlloc_3001_, 2, v_exprs_2936_);
lean_ctor_set(v_reuseFailAlloc_3001_, 3, v_parents_2937_);
lean_ctor_set(v_reuseFailAlloc_3001_, 4, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_3001_, 5, v_appMap_2939_);
lean_ctor_set(v_reuseFailAlloc_3001_, 6, v_indicesFound_2940_);
lean_ctor_set(v_reuseFailAlloc_3001_, 7, v_newFacts_2941_);
lean_ctor_set(v_reuseFailAlloc_3001_, 8, v_nextIdx_2943_);
lean_ctor_set(v_reuseFailAlloc_3001_, 9, v_newRawFacts_2944_);
lean_ctor_set(v_reuseFailAlloc_3001_, 10, v_facts_2945_);
lean_ctor_set(v_reuseFailAlloc_3001_, 11, v_extThms_2946_);
lean_ctor_set(v_reuseFailAlloc_3001_, 12, v_ematch_2947_);
lean_ctor_set(v_reuseFailAlloc_3001_, 13, v_inj_2948_);
lean_ctor_set(v_reuseFailAlloc_3001_, 14, v_split_2949_);
lean_ctor_set(v_reuseFailAlloc_3001_, 15, v_clean_2950_);
lean_ctor_set(v_reuseFailAlloc_3001_, 16, v_sstates_2951_);
lean_ctor_set_uint8(v_reuseFailAlloc_3001_, sizeof(void*)*17, v_inconsistent_2942_);
v___x_2958_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2960_; 
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2958_);
v___x_2960_ = v___x_2932_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_mvarId_2930_);
v___x_2960_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_st_ref_set(v___y_2851_, v___x_2960_);
lean_inc_ref(v_rootNew_2848_);
lean_inc_ref(v_next_2869_);
lean_inc_ref_n(v_self_2868_, 3);
v___x_2962_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v___x_2962_, 0, v_self_2868_);
lean_ctor_set(v___x_2962_, 1, v_next_2869_);
lean_ctor_set(v___x_2962_, 2, v_rootNew_2848_);
lean_ctor_set(v___x_2962_, 3, v_self_2868_);
lean_ctor_set(v___x_2962_, 4, v_target_x3f_2871_);
lean_ctor_set(v___x_2962_, 5, v_proof_x3f_2872_);
lean_ctor_set(v___x_2962_, 6, v_size_2874_);
lean_ctor_set(v___x_2962_, 7, v_idx_2879_);
lean_ctor_set(v___x_2962_, 8, v_generation_2880_);
lean_ctor_set(v___x_2962_, 9, v_mt_2881_);
lean_ctor_set(v___x_2962_, 10, v_sTerms_2882_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*11, v_flipped_2873_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*11 + 1, v_interpreted_2875_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*11 + 2, v_ctor_2876_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*11 + 3, v_hasLambdas_2877_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*11 + 4, v_heqProofs_2878_);
lean_ctor_set_uint8(v___x_2962_, sizeof(void*)*11 + 5, v_funCC_2883_);
v___x_2963_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2868_, v___x_2962_, v___y_2851_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref(v___x_2963_);
v___x_2964_ = lean_st_ref_get(v___y_2851_);
lean_inc(v_fst_2924_);
v___x_2965_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2964_, v_fst_2924_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v_self_2967_; lean_object* v_next_2968_; lean_object* v_root_2969_; lean_object* v_target_x3f_2970_; lean_object* v_proof_x3f_2971_; uint8_t v_flipped_2972_; lean_object* v_size_2973_; uint8_t v_interpreted_2974_; uint8_t v_ctor_2975_; uint8_t v_hasLambdas_2976_; uint8_t v_heqProofs_2977_; lean_object* v_idx_2978_; lean_object* v_generation_2979_; lean_object* v_mt_2980_; lean_object* v_sTerms_2981_; uint8_t v_funCC_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2990_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___x_2965_);
v_self_2967_ = lean_ctor_get(v_a_2966_, 0);
v_next_2968_ = lean_ctor_get(v_a_2966_, 1);
v_root_2969_ = lean_ctor_get(v_a_2966_, 2);
v_target_x3f_2970_ = lean_ctor_get(v_a_2966_, 4);
v_proof_x3f_2971_ = lean_ctor_get(v_a_2966_, 5);
v_flipped_2972_ = lean_ctor_get_uint8(v_a_2966_, sizeof(void*)*11);
v_size_2973_ = lean_ctor_get(v_a_2966_, 6);
v_interpreted_2974_ = lean_ctor_get_uint8(v_a_2966_, sizeof(void*)*11 + 1);
v_ctor_2975_ = lean_ctor_get_uint8(v_a_2966_, sizeof(void*)*11 + 2);
v_hasLambdas_2976_ = lean_ctor_get_uint8(v_a_2966_, sizeof(void*)*11 + 3);
v_heqProofs_2977_ = lean_ctor_get_uint8(v_a_2966_, sizeof(void*)*11 + 4);
v_idx_2978_ = lean_ctor_get(v_a_2966_, 7);
v_generation_2979_ = lean_ctor_get(v_a_2966_, 8);
v_mt_2980_ = lean_ctor_get(v_a_2966_, 9);
v_sTerms_2981_ = lean_ctor_get(v_a_2966_, 10);
v_funCC_2982_ = lean_ctor_get_uint8(v_a_2966_, sizeof(void*)*11 + 5);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_a_2966_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v_a_2966_, 3);
lean_dec(v_unused_2991_);
v___x_2984_ = v_a_2966_;
v_isShared_2985_ = v_isSharedCheck_2990_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_sTerms_2981_);
lean_inc(v_mt_2980_);
lean_inc(v_generation_2979_);
lean_inc(v_idx_2978_);
lean_inc(v_size_2973_);
lean_inc(v_proof_x3f_2971_);
lean_inc(v_target_x3f_2970_);
lean_inc(v_root_2969_);
lean_inc(v_next_2968_);
lean_inc(v_self_2967_);
lean_dec(v_a_2966_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2990_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 3, v_self_2868_);
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_self_2967_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_next_2968_);
lean_ctor_set(v_reuseFailAlloc_2989_, 2, v_root_2969_);
lean_ctor_set(v_reuseFailAlloc_2989_, 3, v_self_2868_);
lean_ctor_set(v_reuseFailAlloc_2989_, 4, v_target_x3f_2970_);
lean_ctor_set(v_reuseFailAlloc_2989_, 5, v_proof_x3f_2971_);
lean_ctor_set(v_reuseFailAlloc_2989_, 6, v_size_2973_);
lean_ctor_set(v_reuseFailAlloc_2989_, 7, v_idx_2978_);
lean_ctor_set(v_reuseFailAlloc_2989_, 8, v_generation_2979_);
lean_ctor_set(v_reuseFailAlloc_2989_, 9, v_mt_2980_);
lean_ctor_set(v_reuseFailAlloc_2989_, 10, v_sTerms_2981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2989_, sizeof(void*)*11, v_flipped_2972_);
lean_ctor_set_uint8(v_reuseFailAlloc_2989_, sizeof(void*)*11 + 1, v_interpreted_2974_);
lean_ctor_set_uint8(v_reuseFailAlloc_2989_, sizeof(void*)*11 + 2, v_ctor_2975_);
lean_ctor_set_uint8(v_reuseFailAlloc_2989_, sizeof(void*)*11 + 3, v_hasLambdas_2976_);
lean_ctor_set_uint8(v_reuseFailAlloc_2989_, sizeof(void*)*11 + 4, v_heqProofs_2977_);
lean_ctor_set_uint8(v_reuseFailAlloc_2989_, sizeof(void*)*11 + 5, v_funCC_2982_);
v___x_2987_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_2924_, v___x_2987_, v___y_2851_);
v___y_2902_ = v___x_2988_;
goto v___jp_2901_;
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec(v_fst_2924_);
lean_dec_ref(v_next_2869_);
lean_dec_ref(v_self_2868_);
lean_del_object(v___x_2866_);
lean_del_object(v___x_2861_);
lean_dec(v_snd_2859_);
lean_dec_ref(v_rootNew_2848_);
v_a_2992_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2965_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2965_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_dec(v_fst_2924_);
lean_dec_ref(v_self_2868_);
v___y_2902_ = v___x_2963_;
goto v___jp_2901_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2924_);
lean_dec(v_sTerms_2882_);
lean_dec(v_mt_2881_);
lean_dec(v_generation_2880_);
lean_dec(v_idx_2879_);
lean_dec(v_size_2874_);
lean_dec(v_proof_x3f_2872_);
lean_dec(v_target_x3f_2871_);
lean_dec_ref(v_self_2868_);
goto v___jp_2888_;
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec(v_fst_2924_);
lean_dec(v_sTerms_2882_);
lean_dec(v_mt_2881_);
lean_dec(v_generation_2880_);
lean_dec(v_idx_2879_);
lean_dec(v_size_2874_);
lean_dec(v_proof_x3f_2872_);
lean_dec(v_target_x3f_2871_);
lean_dec_ref(v_next_2869_);
lean_dec_ref(v_self_2868_);
lean_del_object(v___x_2866_);
lean_del_object(v___x_2861_);
lean_dec(v_snd_2859_);
lean_dec_ref(v_rootNew_2848_);
v_a_3004_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2925_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2925_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
else
{
lean_dec(v_sTerms_2882_);
lean_dec(v_mt_2881_);
lean_dec(v_generation_2880_);
lean_dec(v_idx_2879_);
lean_dec(v_size_2874_);
lean_dec(v_proof_x3f_2872_);
lean_dec(v_target_x3f_2871_);
lean_dec_ref(v_self_2868_);
goto v___jp_2888_;
}
}
}
}
else
{
lean_dec_ref(v___x_2912_);
lean_dec(v_sTerms_2882_);
lean_dec(v_mt_2881_);
lean_dec(v_generation_2880_);
lean_dec(v_idx_2879_);
lean_dec(v_size_2874_);
lean_dec(v_proof_x3f_2872_);
lean_dec(v_target_x3f_2871_);
lean_dec_ref(v_self_2868_);
v___y_2902_ = v___x_2913_;
goto v___jp_2901_;
}
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_del_object(v___x_2861_);
lean_dec(v_snd_2859_);
lean_dec_ref(v_rootNew_2848_);
v_a_3016_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2863_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2863_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3026_, lean_object* v_rootNew_3027_, lean_object* v_a_3028_, lean_object* v_b_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
uint8_t v_a_27771__boxed_3037_; lean_object* v_res_3038_; 
v_a_27771__boxed_3037_ = lean_unbox(v_a_3028_);
v_res_3038_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3026_, v_rootNew_3027_, v_a_27771__boxed_3037_, v_b_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v_lhs_3026_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3039_, lean_object* v_rootNew_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3040_, v_a_3045_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; lean_object* v___x_3057_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref(v___x_3052_);
v___x_3054_ = lean_box(0);
lean_inc_ref(v_lhs_3039_);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v_lhs_3039_);
v___x_3056_ = lean_unbox(v_a_3053_);
lean_dec(v_a_3053_);
v___x_3057_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3039_, v_rootNew_3040_, v___x_3056_, v___x_3055_, v_a_3041_, v_a_3045_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
lean_dec_ref(v_lhs_3039_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3071_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3071_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3071_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v_fst_3062_; 
v_fst_3062_ = lean_ctor_get(v_a_3058_, 0);
lean_inc(v_fst_3062_);
lean_dec(v_a_3058_);
if (lean_obj_tag(v_fst_3062_) == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = lean_box(0);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3063_);
v___x_3065_ = v___x_3060_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
else
{
lean_object* v_val_3067_; lean_object* v___x_3069_; 
v_val_3067_ = lean_ctor_get(v_fst_3062_, 0);
lean_inc(v_val_3067_);
lean_dec_ref(v_fst_3062_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v_val_3067_);
v___x_3069_ = v___x_3060_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_val_3067_);
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
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
v_a_3072_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3057_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3057_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v_rootNew_3040_);
lean_dec_ref(v_lhs_3039_);
v_a_3080_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3052_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3052_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3088_, lean_object* v_rootNew_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3088_, v_rootNew_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec(v_a_3090_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3102_, lean_object* v_00_u03b2_3103_, lean_object* v_x_3104_, lean_object* v_x_3105_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3102_, v_x_3104_, v_x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3107_, lean_object* v_00_u03b2_3108_, lean_object* v_x_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3107_, v_x_3109_, v_x_3110_, v_x_3111_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3113_, lean_object* v_rootNew_3114_, uint8_t v_a_3115_, lean_object* v_b_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3113_, v_rootNew_3114_, v_a_3115_, v_b_3116_, v___y_3117_, v___y_3121_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3129_, lean_object* v_rootNew_3130_, lean_object* v_a_3131_, lean_object* v_b_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
uint8_t v_a_28119__boxed_3144_; lean_object* v_res_3145_; 
v_a_28119__boxed_3144_ = lean_unbox(v_a_3131_);
v_res_3145_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3129_, v_rootNew_3130_, v_a_28119__boxed_3144_, v_b_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v_lhs_3129_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3146_, lean_object* v_00_u03b2_3147_, lean_object* v_x_3148_, size_t v_x_3149_, lean_object* v_x_3150_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3146_, v_x_3148_, v_x_3149_, v_x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3152_, lean_object* v_00_u03b2_3153_, lean_object* v_x_3154_, lean_object* v_x_3155_, lean_object* v_x_3156_){
_start:
{
size_t v_x_28159__boxed_3157_; lean_object* v_res_3158_; 
v_x_28159__boxed_3157_ = lean_unbox_usize(v_x_3155_);
lean_dec(v_x_3155_);
v_res_3158_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3152_, v_00_u03b2_3153_, v_x_3154_, v_x_28159__boxed_3157_, v_x_3156_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3159_, lean_object* v_00_u03b2_3160_, lean_object* v_x_3161_, size_t v_x_3162_, size_t v_x_3163_, lean_object* v_x_3164_, lean_object* v_x_3165_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3159_, v_x_3161_, v_x_3162_, v_x_3163_, v_x_3164_, v_x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3167_, lean_object* v_00_u03b2_3168_, lean_object* v_x_3169_, lean_object* v_x_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_, lean_object* v_x_3173_){
_start:
{
size_t v_x_28173__boxed_3174_; size_t v_x_28174__boxed_3175_; lean_object* v_res_3176_; 
v_x_28173__boxed_3174_ = lean_unbox_usize(v_x_3170_);
lean_dec(v_x_3170_);
v_x_28174__boxed_3175_ = lean_unbox_usize(v_x_3171_);
lean_dec(v_x_3171_);
v_res_3176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3167_, v_00_u03b2_3168_, v_x_3169_, v_x_28173__boxed_3174_, v_x_28174__boxed_3175_, v_x_3172_, v_x_3173_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3177_, lean_object* v_00_u03b2_3178_, lean_object* v_keys_3179_, lean_object* v_vals_3180_, lean_object* v_heq_3181_, lean_object* v_i_3182_, lean_object* v_k_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3177_, v_keys_3179_, v_vals_3180_, v_i_3182_, v_k_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3185_, lean_object* v_00_u03b2_3186_, lean_object* v_keys_3187_, lean_object* v_vals_3188_, lean_object* v_heq_3189_, lean_object* v_i_3190_, lean_object* v_k_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3185_, v_00_u03b2_3186_, v_keys_3187_, v_vals_3188_, v_heq_3189_, v_i_3190_, v_k_3191_);
lean_dec_ref(v_vals_3188_);
lean_dec_ref(v_keys_3187_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3193_, lean_object* v_00_u03b2_3194_, lean_object* v_n_3195_, lean_object* v_k_3196_, lean_object* v_v_3197_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3193_, v_n_3195_, v_k_3196_, v_v_3197_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3199_, lean_object* v_00_u03b2_3200_, size_t v_depth_3201_, lean_object* v_keys_3202_, lean_object* v_vals_3203_, lean_object* v_heq_3204_, lean_object* v_i_3205_, lean_object* v_entries_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3199_, v_depth_3201_, v_keys_3202_, v_vals_3203_, v_i_3205_, v_entries_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3208_, lean_object* v_00_u03b2_3209_, lean_object* v_depth_3210_, lean_object* v_keys_3211_, lean_object* v_vals_3212_, lean_object* v_heq_3213_, lean_object* v_i_3214_, lean_object* v_entries_3215_){
_start:
{
size_t v_depth_boxed_3216_; lean_object* v_res_3217_; 
v_depth_boxed_3216_ = lean_unbox_usize(v_depth_3210_);
lean_dec(v_depth_3210_);
v_res_3217_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3208_, v_00_u03b2_3209_, v_depth_boxed_3216_, v_keys_3211_, v_vals_3212_, v_heq_3213_, v_i_3214_, v_entries_3215_);
lean_dec_ref(v_vals_3212_);
lean_dec_ref(v_keys_3211_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3218_, lean_object* v_00_u03b2_3219_, lean_object* v_x_3220_, lean_object* v_x_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3218_, v_x_3220_, v_x_3221_, v_x_3222_, v_x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3225_, lean_object* v_b_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
if (lean_obj_tag(v_as_x27_3225_) == 0)
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v_b_3226_);
return v___x_3238_;
}
else
{
lean_object* v_head_3239_; lean_object* v_tail_3240_; lean_object* v___x_3241_; 
v_head_3239_ = lean_ctor_get(v_as_x27_3225_, 0);
lean_inc(v_head_3239_);
v_tail_3240_ = lean_ctor_get(v_as_x27_3225_, 1);
lean_inc(v_tail_3240_);
lean_dec_ref(v_as_x27_3225_);
v___x_3241_ = l_Lean_Meta_Grind_propagateUp(v_head_3239_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v___x_3242_; 
lean_dec_ref(v___x_3241_);
v___x_3242_ = lean_box(0);
v_as_x27_3225_ = v_tail_3240_;
v_b_3226_ = v___x_3242_;
goto _start;
}
else
{
lean_dec(v_tail_3240_);
return v___x_3241_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3244_, lean_object* v_b_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3244_, v_b_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec(v___y_3246_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3258_, lean_object* v_b_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
if (lean_obj_tag(v_as_x27_3258_) == 0)
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_b_3259_);
return v___x_3271_;
}
else
{
lean_object* v_head_3272_; lean_object* v_tail_3273_; lean_object* v___x_3274_; 
v_head_3272_ = lean_ctor_get(v_as_x27_3258_, 0);
lean_inc(v_head_3272_);
v_tail_3273_ = lean_ctor_get(v_as_x27_3258_, 1);
lean_inc(v_tail_3273_);
lean_dec_ref(v_as_x27_3258_);
v___x_3274_ = l_Lean_Meta_Grind_propagateDown(v_head_3272_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v___x_3275_; 
lean_dec_ref(v___x_3274_);
v___x_3275_ = lean_box(0);
v_as_x27_3258_ = v_tail_3273_;
v_b_3259_ = v___x_3275_;
goto _start;
}
else
{
lean_dec(v_tail_3273_);
return v___x_3274_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3277_, lean_object* v_b_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3277_, v_b_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec(v___y_3279_);
return v_res_3290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_cls_3294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3295_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3296_ = l_Lean_Name_append(v___x_3295_, v_cls_3294_);
return v___x_3296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3299_ = l_Lean_stringToMessageData(v___x_3298_);
return v___x_3299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3302_ = l_Lean_stringToMessageData(v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3305_ = l_Lean_stringToMessageData(v___x_3304_);
return v___x_3305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3308_ = l_Lean_stringToMessageData(v___x_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3309_, uint8_t v_isHEq_3310_, lean_object* v_lhs_3311_, lean_object* v_rhs_3312_, lean_object* v_lhsNode_3313_, lean_object* v_rhsNode_3314_, lean_object* v_lhsRoot_3315_, lean_object* v_rhsRoot_3316_, uint8_t v_flipped_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_){
_start:
{
lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3382_; uint8_t v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; uint8_t v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; uint8_t v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; uint8_t v___y_3413_; lean_object* v___y_3414_; uint8_t v___y_3415_; uint8_t v___y_3416_; lean_object* v___y_3446_; lean_object* v___y_3447_; uint8_t v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; uint8_t v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3473_; uint8_t v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; uint8_t v___y_3478_; lean_object* v___y_3479_; uint8_t v___y_3480_; uint8_t v___y_3481_; uint8_t v___y_3483_; uint8_t v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v_options_3563_; lean_object* v_inheritedTraceOptions_3564_; uint8_t v_hasTrace_3565_; lean_object* v_cls_3566_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v_fns_u2082_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v_fns_u2081_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; 
v_options_3563_ = lean_ctor_get(v_a_3326_, 2);
v_inheritedTraceOptions_3564_ = lean_ctor_get(v_a_3326_, 13);
v_hasTrace_3565_ = lean_ctor_get_uint8(v_options_3563_, sizeof(void*)*1);
v_cls_3566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3565_ == 0)
{
v___y_3685_ = v_a_3318_;
v___y_3686_ = v_a_3319_;
v___y_3687_ = v_a_3320_;
v___y_3688_ = v_a_3321_;
v___y_3689_ = v_a_3322_;
v___y_3690_ = v_a_3323_;
v___y_3691_ = v_a_3324_;
v___y_3692_ = v_a_3325_;
v___y_3693_ = v_a_3326_;
v___y_3694_ = v_a_3327_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3764_; uint8_t v___x_3765_; 
v___x_3764_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3765_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3564_, v_options_3563_, v___x_3764_);
if (v___x_3765_ == 0)
{
v___y_3685_ = v_a_3318_;
v___y_3686_ = v_a_3319_;
v___y_3687_ = v_a_3320_;
v___y_3688_ = v_a_3321_;
v___y_3689_ = v_a_3322_;
v___y_3690_ = v_a_3323_;
v___y_3691_ = v_a_3324_;
v___y_3692_ = v_a_3325_;
v___y_3693_ = v_a_3326_;
v___y_3694_ = v_a_3327_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_Meta_Grind_updateLastTag(v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v___x_3767_; 
lean_dec_ref(v___x_3766_);
lean_inc_ref(v_lhs_3311_);
v___x_3767_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3311_, v_a_3318_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3769_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref(v___x_3767_);
lean_inc_ref(v_rhs_3312_);
v___x_3769_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3312_, v_a_3318_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_a_3770_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
lean_ctor_set(v___x_3772_, 1, v_a_3768_);
v___x_3773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3774_);
lean_ctor_set(v___x_3775_, 1, v_a_3770_);
v___x_3776_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3566_, v___x_3775_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_dec_ref(v___x_3776_);
v___y_3685_ = v_a_3318_;
v___y_3686_ = v_a_3319_;
v___y_3687_ = v_a_3320_;
v___y_3688_ = v_a_3321_;
v___y_3689_ = v_a_3322_;
v___y_3690_ = v_a_3323_;
v___y_3691_ = v_a_3324_;
v___y_3692_ = v_a_3325_;
v___y_3693_ = v_a_3326_;
v___y_3694_ = v_a_3327_;
goto v___jp_3684_;
}
else
{
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhsNode_3313_);
lean_dec_ref(v_rhs_3312_);
lean_dec_ref(v_lhs_3311_);
lean_dec_ref(v_proof_3309_);
return v___x_3776_;
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec(v_a_3768_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhsNode_3313_);
lean_dec_ref(v_rhs_3312_);
lean_dec_ref(v_lhs_3311_);
lean_dec_ref(v_proof_3309_);
v_a_3777_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3769_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3769_);
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
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhsNode_3313_);
lean_dec_ref(v_rhs_3312_);
lean_dec_ref(v_lhs_3311_);
lean_dec_ref(v_proof_3309_);
v_a_3785_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3767_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3767_);
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
else
{
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhsNode_3313_);
lean_dec_ref(v_rhs_3312_);
lean_dec_ref(v_lhs_3311_);
lean_dec_ref(v_proof_3309_);
return v___x_3766_;
}
}
}
v___jp_3329_:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3336_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3372_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3349_ = v___x_3346_;
v_isShared_3350_ = v_isSharedCheck_3372_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3372_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
uint8_t v___x_3351_; 
v___x_3351_ = lean_unbox(v_a_3347_);
lean_dec(v_a_3347_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_del_object(v___x_3349_);
v___x_3352_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3333_);
lean_dec(v___y_3333_);
v___x_3353_ = lean_box(0);
v___x_3354_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3352_, v___x_3353_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v___x_3355_; 
lean_dec_ref(v___x_3354_);
lean_inc(v___y_3334_);
v___x_3355_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3334_, v___x_3353_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref(v___x_3355_);
v___x_3356_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3331_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3331_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v___x_3357_; 
lean_dec_ref(v___x_3356_);
v___x_3357_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3330_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3366_; 
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3366_ == 0)
{
lean_object* v_unused_3367_; 
v_unused_3367_ = lean_ctor_get(v___x_3357_, 0);
lean_dec(v_unused_3367_);
v___x_3359_ = v___x_3357_;
v_isShared_3360_ = v_isSharedCheck_3366_;
goto v_resetjp_3358_;
}
else
{
lean_dec(v___x_3357_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3366_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
uint8_t v___x_3361_; 
v___x_3361_ = l_Lean_Expr_isTrue(v___y_3332_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3363_; 
lean_dec(v___y_3334_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3353_);
v___x_3363_ = v___x_3359_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3353_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
else
{
lean_object* v___x_3365_; 
lean_del_object(v___x_3359_);
v___x_3365_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3334_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3334_);
return v___x_3365_;
}
}
}
else
{
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3332_);
return v___x_3357_;
}
}
else
{
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3330_);
return v___x_3356_;
}
}
else
{
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
return v___x_3355_;
}
}
else
{
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
return v___x_3354_;
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
v___x_3368_ = lean_box(0);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3368_);
v___x_3370_ = v___x_3349_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
v_a_3373_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3346_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3346_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
v___jp_3381_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_inc_ref(v___y_3414_);
v___x_3417_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v___x_3417_, 0, v___y_3414_);
lean_ctor_set(v___x_3417_, 1, v___y_3382_);
lean_ctor_set(v___x_3417_, 2, v___y_3393_);
lean_ctor_set(v___x_3417_, 3, v___y_3405_);
lean_ctor_set(v___x_3417_, 4, v___y_3398_);
lean_ctor_set(v___x_3417_, 5, v___y_3406_);
lean_ctor_set(v___x_3417_, 6, v___y_3411_);
lean_ctor_set(v___x_3417_, 7, v___y_3392_);
lean_ctor_set(v___x_3417_, 8, v___y_3385_);
lean_ctor_set(v___x_3417_, 9, v___y_3401_);
lean_ctor_set(v___x_3417_, 10, v___y_3389_);
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*11, v___y_3415_);
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*11 + 1, v___y_3396_);
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*11 + 2, v___y_3413_);
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*11 + 3, v___y_3408_);
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*11 + 4, v___y_3416_);
lean_ctor_set_uint8(v___x_3417_, sizeof(void*)*11 + 5, v___y_3383_);
lean_inc_ref(v___y_3390_);
v___x_3418_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3390_, v___x_3417_, v___y_3403_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v___x_3419_; 
lean_dec_ref(v___x_3418_);
lean_inc_ref(v___y_3384_);
v___x_3419_ = l_Lean_Meta_Grind_propagateBeta(v___y_3384_, v___y_3386_, v___y_3403_, v___y_3402_, v___y_3410_, v___y_3394_, v___y_3404_, v___y_3412_, v___y_3409_, v___y_3391_, v___y_3388_, v___y_3387_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v___x_3420_; 
lean_dec_ref(v___x_3419_);
lean_inc_ref(v___y_3407_);
v___x_3420_ = l_Lean_Meta_Grind_propagateBeta(v___y_3407_, v___y_3397_, v___y_3403_, v___y_3402_, v___y_3410_, v___y_3394_, v___y_3404_, v___y_3412_, v___y_3409_, v___y_3391_, v___y_3388_, v___y_3387_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v___x_3421_; 
lean_dec_ref(v___x_3420_);
v___x_3421_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3316_, v_lhsRoot_3315_, v___y_3403_, v___y_3409_, v___y_3391_, v___y_3388_, v___y_3387_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3395_, v___y_3403_);
lean_dec_ref(v___y_3395_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v___x_3424_; 
lean_dec_ref(v___x_3423_);
lean_inc_ref(v___y_3390_);
lean_inc(v___y_3399_);
v___x_3424_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3399_, v___y_3390_, v___y_3403_, v___y_3402_, v___y_3410_, v___y_3394_, v___y_3404_, v___y_3412_, v___y_3409_, v___y_3391_, v___y_3388_, v___y_3387_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v___x_3425_; 
lean_dec_ref(v___x_3424_);
v___x_3425_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3403_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; uint8_t v___x_3427_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref(v___x_3425_);
v___x_3427_ = lean_unbox(v_a_3426_);
lean_dec(v_a_3426_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
v___x_3428_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3414_, v___y_3403_, v___y_3402_, v___y_3410_, v___y_3394_, v___y_3404_, v___y_3412_, v___y_3409_, v___y_3391_, v___y_3388_, v___y_3387_);
lean_dec_ref(v___y_3414_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_dec_ref(v___x_3428_);
v___y_3330_ = v_a_3422_;
v___y_3331_ = v___y_3384_;
v___y_3332_ = v___y_3390_;
v___y_3333_ = v___y_3399_;
v___y_3334_ = v___y_3400_;
v___y_3335_ = v___y_3407_;
v___y_3336_ = v___y_3403_;
v___y_3337_ = v___y_3402_;
v___y_3338_ = v___y_3410_;
v___y_3339_ = v___y_3394_;
v___y_3340_ = v___y_3404_;
v___y_3341_ = v___y_3412_;
v___y_3342_ = v___y_3409_;
v___y_3343_ = v___y_3391_;
v___y_3344_ = v___y_3388_;
v___y_3345_ = v___y_3387_;
goto v___jp_3329_;
}
else
{
lean_dec(v_a_3422_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___y_3384_);
return v___x_3428_;
}
}
else
{
lean_dec_ref(v___y_3414_);
v___y_3330_ = v_a_3422_;
v___y_3331_ = v___y_3384_;
v___y_3332_ = v___y_3390_;
v___y_3333_ = v___y_3399_;
v___y_3334_ = v___y_3400_;
v___y_3335_ = v___y_3407_;
v___y_3336_ = v___y_3403_;
v___y_3337_ = v___y_3402_;
v___y_3338_ = v___y_3410_;
v___y_3339_ = v___y_3394_;
v___y_3340_ = v___y_3404_;
v___y_3341_ = v___y_3412_;
v___y_3342_ = v___y_3409_;
v___y_3343_ = v___y_3391_;
v___y_3344_ = v___y_3388_;
v___y_3345_ = v___y_3387_;
goto v___jp_3329_;
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec(v_a_3422_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___y_3384_);
v_a_3429_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3425_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3425_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
else
{
lean_dec(v_a_3422_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___y_3384_);
return v___x_3424_;
}
}
else
{
lean_dec(v_a_3422_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___y_3384_);
return v___x_3423_;
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3395_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___y_3384_);
v_a_3437_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3421_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3421_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
else
{
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3395_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___y_3384_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
return v___x_3420_;
}
}
else
{
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3397_);
lean_dec_ref(v___y_3395_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___y_3384_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
return v___x_3419_;
}
}
else
{
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3397_);
lean_dec_ref(v___y_3395_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___y_3386_);
lean_dec_ref(v___y_3384_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
return v___x_3418_;
}
}
v___jp_3445_:
{
if (v_isHEq_3310_ == 0)
{
if (v___y_3474_ == 0)
{
v___y_3382_ = v___y_3446_;
v___y_3383_ = v___y_3448_;
v___y_3384_ = v___y_3447_;
v___y_3385_ = v___y_3449_;
v___y_3386_ = v___y_3450_;
v___y_3387_ = v___y_3454_;
v___y_3388_ = v___y_3453_;
v___y_3389_ = v___y_3452_;
v___y_3390_ = v___y_3451_;
v___y_3391_ = v___y_3455_;
v___y_3392_ = v___y_3456_;
v___y_3393_ = v___y_3457_;
v___y_3394_ = v___y_3458_;
v___y_3395_ = v___y_3459_;
v___y_3396_ = v___y_3460_;
v___y_3397_ = v___y_3461_;
v___y_3398_ = v___y_3462_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3464_;
v___y_3401_ = v___y_3465_;
v___y_3402_ = v___y_3466_;
v___y_3403_ = v___y_3467_;
v___y_3404_ = v___y_3468_;
v___y_3405_ = v___y_3469_;
v___y_3406_ = v___y_3470_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3481_;
v___y_3409_ = v___y_3472_;
v___y_3410_ = v___y_3475_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3477_;
v___y_3413_ = v___y_3478_;
v___y_3414_ = v___y_3479_;
v___y_3415_ = v___y_3480_;
v___y_3416_ = v___y_3473_;
goto v___jp_3381_;
}
else
{
v___y_3382_ = v___y_3446_;
v___y_3383_ = v___y_3448_;
v___y_3384_ = v___y_3447_;
v___y_3385_ = v___y_3449_;
v___y_3386_ = v___y_3450_;
v___y_3387_ = v___y_3454_;
v___y_3388_ = v___y_3453_;
v___y_3389_ = v___y_3452_;
v___y_3390_ = v___y_3451_;
v___y_3391_ = v___y_3455_;
v___y_3392_ = v___y_3456_;
v___y_3393_ = v___y_3457_;
v___y_3394_ = v___y_3458_;
v___y_3395_ = v___y_3459_;
v___y_3396_ = v___y_3460_;
v___y_3397_ = v___y_3461_;
v___y_3398_ = v___y_3462_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3464_;
v___y_3401_ = v___y_3465_;
v___y_3402_ = v___y_3466_;
v___y_3403_ = v___y_3467_;
v___y_3404_ = v___y_3468_;
v___y_3405_ = v___y_3469_;
v___y_3406_ = v___y_3470_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3481_;
v___y_3409_ = v___y_3472_;
v___y_3410_ = v___y_3475_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3477_;
v___y_3413_ = v___y_3478_;
v___y_3414_ = v___y_3479_;
v___y_3415_ = v___y_3480_;
v___y_3416_ = v___y_3474_;
goto v___jp_3381_;
}
}
else
{
v___y_3382_ = v___y_3446_;
v___y_3383_ = v___y_3448_;
v___y_3384_ = v___y_3447_;
v___y_3385_ = v___y_3449_;
v___y_3386_ = v___y_3450_;
v___y_3387_ = v___y_3454_;
v___y_3388_ = v___y_3453_;
v___y_3389_ = v___y_3452_;
v___y_3390_ = v___y_3451_;
v___y_3391_ = v___y_3455_;
v___y_3392_ = v___y_3456_;
v___y_3393_ = v___y_3457_;
v___y_3394_ = v___y_3458_;
v___y_3395_ = v___y_3459_;
v___y_3396_ = v___y_3460_;
v___y_3397_ = v___y_3461_;
v___y_3398_ = v___y_3462_;
v___y_3399_ = v___y_3463_;
v___y_3400_ = v___y_3464_;
v___y_3401_ = v___y_3465_;
v___y_3402_ = v___y_3466_;
v___y_3403_ = v___y_3467_;
v___y_3404_ = v___y_3468_;
v___y_3405_ = v___y_3469_;
v___y_3406_ = v___y_3470_;
v___y_3407_ = v___y_3471_;
v___y_3408_ = v___y_3481_;
v___y_3409_ = v___y_3472_;
v___y_3410_ = v___y_3475_;
v___y_3411_ = v___y_3476_;
v___y_3412_ = v___y_3477_;
v___y_3413_ = v___y_3478_;
v___y_3414_ = v___y_3479_;
v___y_3415_ = v___y_3480_;
v___y_3416_ = v_isHEq_3310_;
goto v___jp_3381_;
}
}
v___jp_3482_:
{
lean_object* v___x_3505_; 
v___x_3505_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3493_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_dec_ref(v___x_3505_);
v___x_3506_ = lean_st_ref_get(v___y_3495_);
v___x_3507_ = lean_st_ref_get(v___y_3495_);
lean_inc_ref(v___y_3487_);
v___x_3508_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3507_, v___y_3487_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v_self_3510_; lean_object* v_root_3511_; lean_object* v_congr_3512_; lean_object* v_target_x3f_3513_; lean_object* v_proof_x3f_3514_; uint8_t v_flipped_3515_; lean_object* v_size_3516_; uint8_t v_interpreted_3517_; uint8_t v_ctor_3518_; uint8_t v_hasLambdas_3519_; uint8_t v_heqProofs_3520_; lean_object* v_idx_3521_; lean_object* v_generation_3522_; lean_object* v_mt_3523_; lean_object* v_sTerms_3524_; uint8_t v_funCC_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3553_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3509_);
lean_dec_ref(v___x_3508_);
v_self_3510_ = lean_ctor_get(v_a_3509_, 0);
v_root_3511_ = lean_ctor_get(v_a_3509_, 2);
v_congr_3512_ = lean_ctor_get(v_a_3509_, 3);
v_target_x3f_3513_ = lean_ctor_get(v_a_3509_, 4);
v_proof_x3f_3514_ = lean_ctor_get(v_a_3509_, 5);
v_flipped_3515_ = lean_ctor_get_uint8(v_a_3509_, sizeof(void*)*11);
v_size_3516_ = lean_ctor_get(v_a_3509_, 6);
v_interpreted_3517_ = lean_ctor_get_uint8(v_a_3509_, sizeof(void*)*11 + 1);
v_ctor_3518_ = lean_ctor_get_uint8(v_a_3509_, sizeof(void*)*11 + 2);
v_hasLambdas_3519_ = lean_ctor_get_uint8(v_a_3509_, sizeof(void*)*11 + 3);
v_heqProofs_3520_ = lean_ctor_get_uint8(v_a_3509_, sizeof(void*)*11 + 4);
v_idx_3521_ = lean_ctor_get(v_a_3509_, 7);
v_generation_3522_ = lean_ctor_get(v_a_3509_, 8);
v_mt_3523_ = lean_ctor_get(v_a_3509_, 9);
v_sTerms_3524_ = lean_ctor_get(v_a_3509_, 10);
v_funCC_3525_ = lean_ctor_get_uint8(v_a_3509_, sizeof(void*)*11 + 5);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_a_3509_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; 
v_unused_3554_ = lean_ctor_get(v_a_3509_, 1);
lean_dec(v_unused_3554_);
v___x_3527_ = v_a_3509_;
v_isShared_3528_ = v_isSharedCheck_3553_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_sTerms_3524_);
lean_inc(v_mt_3523_);
lean_inc(v_generation_3522_);
lean_inc(v_idx_3521_);
lean_inc(v_size_3516_);
lean_inc(v_proof_x3f_3514_);
lean_inc(v_target_x3f_3513_);
lean_inc(v_congr_3512_);
lean_inc(v_root_3511_);
lean_inc(v_self_3510_);
lean_dec(v_a_3509_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3553_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v_self_3529_; lean_object* v_next_3530_; lean_object* v_root_3531_; lean_object* v_congr_3532_; lean_object* v_target_x3f_3533_; lean_object* v_proof_x3f_3534_; uint8_t v_flipped_3535_; lean_object* v_size_3536_; uint8_t v_interpreted_3537_; uint8_t v_ctor_3538_; uint8_t v_hasLambdas_3539_; uint8_t v_heqProofs_3540_; lean_object* v_idx_3541_; lean_object* v_generation_3542_; lean_object* v_mt_3543_; lean_object* v_sTerms_3544_; uint8_t v_funCC_3545_; lean_object* v___x_3547_; 
v_self_3529_ = lean_ctor_get(v_rhsRoot_3316_, 0);
v_next_3530_ = lean_ctor_get(v_rhsRoot_3316_, 1);
v_root_3531_ = lean_ctor_get(v_rhsRoot_3316_, 2);
v_congr_3532_ = lean_ctor_get(v_rhsRoot_3316_, 3);
v_target_x3f_3533_ = lean_ctor_get(v_rhsRoot_3316_, 4);
v_proof_x3f_3534_ = lean_ctor_get(v_rhsRoot_3316_, 5);
v_flipped_3535_ = lean_ctor_get_uint8(v_rhsRoot_3316_, sizeof(void*)*11);
v_size_3536_ = lean_ctor_get(v_rhsRoot_3316_, 6);
v_interpreted_3537_ = lean_ctor_get_uint8(v_rhsRoot_3316_, sizeof(void*)*11 + 1);
v_ctor_3538_ = lean_ctor_get_uint8(v_rhsRoot_3316_, sizeof(void*)*11 + 2);
v_hasLambdas_3539_ = lean_ctor_get_uint8(v_rhsRoot_3316_, sizeof(void*)*11 + 3);
v_heqProofs_3540_ = lean_ctor_get_uint8(v_rhsRoot_3316_, sizeof(void*)*11 + 4);
v_idx_3541_ = lean_ctor_get(v_rhsRoot_3316_, 7);
v_generation_3542_ = lean_ctor_get(v_rhsRoot_3316_, 8);
v_mt_3543_ = lean_ctor_get(v_rhsRoot_3316_, 9);
v_sTerms_3544_ = lean_ctor_get(v_rhsRoot_3316_, 10);
v_funCC_3545_ = lean_ctor_get_uint8(v_rhsRoot_3316_, sizeof(void*)*11 + 5);
lean_inc_ref(v_next_3530_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 1, v_next_3530_);
v___x_3547_ = v___x_3527_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_self_3510_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_next_3530_);
lean_ctor_set(v_reuseFailAlloc_3552_, 2, v_root_3511_);
lean_ctor_set(v_reuseFailAlloc_3552_, 3, v_congr_3512_);
lean_ctor_set(v_reuseFailAlloc_3552_, 4, v_target_x3f_3513_);
lean_ctor_set(v_reuseFailAlloc_3552_, 5, v_proof_x3f_3514_);
lean_ctor_set(v_reuseFailAlloc_3552_, 6, v_size_3516_);
lean_ctor_set(v_reuseFailAlloc_3552_, 7, v_idx_3521_);
lean_ctor_set(v_reuseFailAlloc_3552_, 8, v_generation_3522_);
lean_ctor_set(v_reuseFailAlloc_3552_, 9, v_mt_3523_);
lean_ctor_set(v_reuseFailAlloc_3552_, 10, v_sTerms_3524_);
lean_ctor_set_uint8(v_reuseFailAlloc_3552_, sizeof(void*)*11, v_flipped_3515_);
lean_ctor_set_uint8(v_reuseFailAlloc_3552_, sizeof(void*)*11 + 1, v_interpreted_3517_);
lean_ctor_set_uint8(v_reuseFailAlloc_3552_, sizeof(void*)*11 + 2, v_ctor_3518_);
lean_ctor_set_uint8(v_reuseFailAlloc_3552_, sizeof(void*)*11 + 3, v_hasLambdas_3519_);
lean_ctor_set_uint8(v_reuseFailAlloc_3552_, sizeof(void*)*11 + 4, v_heqProofs_3520_);
lean_ctor_set_uint8(v_reuseFailAlloc_3552_, sizeof(void*)*11 + 5, v_funCC_3525_);
v___x_3547_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3489_, v___x_3547_, v___y_3495_);
if (lean_obj_tag(v___x_3548_) == 0)
{
uint8_t v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec_ref(v___x_3548_);
v___x_3549_ = 0;
v___x_3550_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3506_, v_lhs_3311_, v___x_3549_);
v___x_3551_ = lean_nat_add(v_size_3536_, v___y_3488_);
lean_dec(v___y_3488_);
if (v_hasLambdas_3539_ == 0)
{
lean_inc_ref(v_self_3529_);
lean_inc(v_proof_x3f_3534_);
lean_inc_ref(v_congr_3532_);
lean_inc(v_mt_3543_);
lean_inc(v_target_x3f_3533_);
lean_inc_ref(v_root_3531_);
lean_inc(v_idx_3541_);
lean_inc(v_sTerms_3544_);
lean_inc(v_generation_3542_);
v___y_3446_ = v___y_3485_;
v___y_3447_ = v___y_3486_;
v___y_3448_ = v_funCC_3545_;
v___y_3449_ = v_generation_3542_;
v___y_3450_ = v___y_3491_;
v___y_3451_ = v___y_3492_;
v___y_3452_ = v_sTerms_3544_;
v___y_3453_ = v___y_3503_;
v___y_3454_ = v___y_3504_;
v___y_3455_ = v___y_3502_;
v___y_3456_ = v_idx_3541_;
v___y_3457_ = v_root_3531_;
v___y_3458_ = v___y_3498_;
v___y_3459_ = v___y_3487_;
v___y_3460_ = v_interpreted_3537_;
v___y_3461_ = v___y_3490_;
v___y_3462_ = v_target_x3f_3533_;
v___y_3463_ = v___y_3493_;
v___y_3464_ = v___x_3550_;
v___y_3465_ = v_mt_3543_;
v___y_3466_ = v___y_3496_;
v___y_3467_ = v___y_3495_;
v___y_3468_ = v___y_3499_;
v___y_3469_ = v_congr_3532_;
v___y_3470_ = v_proof_x3f_3534_;
v___y_3471_ = v___y_3494_;
v___y_3472_ = v___y_3501_;
v___y_3473_ = v___y_3484_;
v___y_3474_ = v_heqProofs_3540_;
v___y_3475_ = v___y_3497_;
v___y_3476_ = v___x_3551_;
v___y_3477_ = v___y_3500_;
v___y_3478_ = v_ctor_3538_;
v___y_3479_ = v_self_3529_;
v___y_3480_ = v_flipped_3535_;
v___y_3481_ = v___y_3483_;
goto v___jp_3445_;
}
else
{
lean_inc_ref(v_self_3529_);
lean_inc(v_proof_x3f_3534_);
lean_inc_ref(v_congr_3532_);
lean_inc(v_mt_3543_);
lean_inc(v_target_x3f_3533_);
lean_inc_ref(v_root_3531_);
lean_inc(v_idx_3541_);
lean_inc(v_sTerms_3544_);
lean_inc(v_generation_3542_);
v___y_3446_ = v___y_3485_;
v___y_3447_ = v___y_3486_;
v___y_3448_ = v_funCC_3545_;
v___y_3449_ = v_generation_3542_;
v___y_3450_ = v___y_3491_;
v___y_3451_ = v___y_3492_;
v___y_3452_ = v_sTerms_3544_;
v___y_3453_ = v___y_3503_;
v___y_3454_ = v___y_3504_;
v___y_3455_ = v___y_3502_;
v___y_3456_ = v_idx_3541_;
v___y_3457_ = v_root_3531_;
v___y_3458_ = v___y_3498_;
v___y_3459_ = v___y_3487_;
v___y_3460_ = v_interpreted_3537_;
v___y_3461_ = v___y_3490_;
v___y_3462_ = v_target_x3f_3533_;
v___y_3463_ = v___y_3493_;
v___y_3464_ = v___x_3550_;
v___y_3465_ = v_mt_3543_;
v___y_3466_ = v___y_3496_;
v___y_3467_ = v___y_3495_;
v___y_3468_ = v___y_3499_;
v___y_3469_ = v_congr_3532_;
v___y_3470_ = v_proof_x3f_3534_;
v___y_3471_ = v___y_3494_;
v___y_3472_ = v___y_3501_;
v___y_3473_ = v___y_3484_;
v___y_3474_ = v_heqProofs_3540_;
v___y_3475_ = v___y_3497_;
v___y_3476_ = v___x_3551_;
v___y_3477_ = v___y_3500_;
v___y_3478_ = v_ctor_3538_;
v___y_3479_ = v_self_3529_;
v___y_3480_ = v_flipped_3535_;
v___y_3481_ = v_hasLambdas_3539_;
goto v___jp_3445_;
}
}
else
{
lean_dec(v___x_3506_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_lhs_3311_);
return v___x_3548_;
}
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_dec(v___x_3506_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_lhs_3311_);
v_a_3555_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3508_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3508_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
else
{
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_lhs_3311_);
return v___x_3505_;
}
}
v___jp_3567_:
{
lean_object* v_self_3583_; lean_object* v_next_3584_; lean_object* v_size_3585_; uint8_t v_hasLambdas_3586_; uint8_t v_heqProofs_3587_; lean_object* v___x_3588_; 
v_self_3583_ = lean_ctor_get(v_lhsRoot_3315_, 0);
v_next_3584_ = lean_ctor_get(v_lhsRoot_3315_, 1);
v_size_3585_ = lean_ctor_get(v_lhsRoot_3315_, 6);
v_hasLambdas_3586_ = lean_ctor_get_uint8(v_lhsRoot_3315_, sizeof(void*)*11 + 3);
v_heqProofs_3587_ = lean_ctor_get_uint8(v_lhsRoot_3315_, sizeof(void*)*11 + 4);
v___x_3588_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3583_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v_root_3590_; lean_object* v___x_3591_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref(v___x_3588_);
v_root_3590_ = lean_ctor_get(v_rhsNode_3314_, 2);
lean_inc_ref_n(v_root_3590_, 2);
lean_dec_ref(v_rhsNode_3314_);
lean_inc_ref(v_lhs_3311_);
v___x_3591_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3311_, v_root_3590_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_options_3592_; uint8_t v_hasTrace_3593_; 
lean_dec_ref(v___x_3591_);
v_options_3592_ = lean_ctor_get(v___y_3581_, 2);
v_hasTrace_3593_ = lean_ctor_get_uint8(v_options_3592_, sizeof(void*)*1);
if (v_hasTrace_3593_ == 0)
{
lean_inc(v_size_3585_);
lean_inc_ref(v_self_3583_);
lean_inc_ref(v_next_3584_);
v___y_3483_ = v_hasLambdas_3586_;
v___y_3484_ = v_heqProofs_3587_;
v___y_3485_ = v_next_3584_;
v___y_3486_ = v___y_3568_;
v___y_3487_ = v_self_3583_;
v___y_3488_ = v_size_3585_;
v___y_3489_ = v___y_3569_;
v___y_3490_ = v_fns_u2082_3572_;
v___y_3491_ = v___y_3570_;
v___y_3492_ = v_root_3590_;
v___y_3493_ = v_a_3589_;
v___y_3494_ = v___y_3571_;
v___y_3495_ = v___y_3573_;
v___y_3496_ = v___y_3574_;
v___y_3497_ = v___y_3575_;
v___y_3498_ = v___y_3576_;
v___y_3499_ = v___y_3577_;
v___y_3500_ = v___y_3578_;
v___y_3501_ = v___y_3579_;
v___y_3502_ = v___y_3580_;
v___y_3503_ = v___y_3581_;
v___y_3504_ = v___y_3582_;
goto v___jp_3482_;
}
else
{
lean_object* v_inheritedTraceOptions_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_inheritedTraceOptions_3594_ = lean_ctor_get(v___y_3581_, 13);
v___x_3595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3596_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3594_, v_options_3592_, v___x_3595_);
if (v___x_3596_ == 0)
{
lean_inc(v_size_3585_);
lean_inc_ref(v_self_3583_);
lean_inc_ref(v_next_3584_);
v___y_3483_ = v_hasLambdas_3586_;
v___y_3484_ = v_heqProofs_3587_;
v___y_3485_ = v_next_3584_;
v___y_3486_ = v___y_3568_;
v___y_3487_ = v_self_3583_;
v___y_3488_ = v_size_3585_;
v___y_3489_ = v___y_3569_;
v___y_3490_ = v_fns_u2082_3572_;
v___y_3491_ = v___y_3570_;
v___y_3492_ = v_root_3590_;
v___y_3493_ = v_a_3589_;
v___y_3494_ = v___y_3571_;
v___y_3495_ = v___y_3573_;
v___y_3496_ = v___y_3574_;
v___y_3497_ = v___y_3575_;
v___y_3498_ = v___y_3576_;
v___y_3499_ = v___y_3577_;
v___y_3500_ = v___y_3578_;
v___y_3501_ = v___y_3579_;
v___y_3502_ = v___y_3580_;
v___y_3503_ = v___y_3581_;
v___y_3504_ = v___y_3582_;
goto v___jp_3482_;
}
else
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Lean_Meta_Grind_updateLastTag(v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v___x_3598_; 
lean_dec_ref(v___x_3597_);
lean_inc_ref(v_lhs_3311_);
v___x_3598_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3311_, v___y_3573_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref(v___x_3598_);
lean_inc_ref(v_root_3590_);
v___x_3600_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3590_, v___y_3573_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref(v___x_3600_);
v___x_3602_ = lean_st_ref_get(v___y_3573_);
lean_inc_ref(v_lhs_3311_);
v___x_3603_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3602_, v_lhs_3311_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref(v___x_3603_);
v___x_3605_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3604_, v___y_3573_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3605_);
v___x_3607_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v_a_3599_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
lean_ctor_set(v___x_3609_, 1, v_a_3601_);
v___x_3610_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
lean_ctor_set(v___x_3612_, 1, v_a_3606_);
v___x_3613_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3566_, v___x_3612_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_dec_ref(v___x_3613_);
lean_inc(v_size_3585_);
lean_inc_ref(v_self_3583_);
lean_inc_ref(v_next_3584_);
v___y_3483_ = v_hasLambdas_3586_;
v___y_3484_ = v_heqProofs_3587_;
v___y_3485_ = v_next_3584_;
v___y_3486_ = v___y_3568_;
v___y_3487_ = v_self_3583_;
v___y_3488_ = v_size_3585_;
v___y_3489_ = v___y_3569_;
v___y_3490_ = v_fns_u2082_3572_;
v___y_3491_ = v___y_3570_;
v___y_3492_ = v_root_3590_;
v___y_3493_ = v_a_3589_;
v___y_3494_ = v___y_3571_;
v___y_3495_ = v___y_3573_;
v___y_3496_ = v___y_3574_;
v___y_3497_ = v___y_3575_;
v___y_3498_ = v___y_3576_;
v___y_3499_ = v___y_3577_;
v___y_3500_ = v___y_3578_;
v___y_3501_ = v___y_3579_;
v___y_3502_ = v___y_3580_;
v___y_3503_ = v___y_3581_;
v___y_3504_ = v___y_3582_;
goto v___jp_3482_;
}
else
{
lean_dec_ref(v_root_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_fns_u2082_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_lhs_3311_);
return v___x_3613_;
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_a_3601_);
lean_dec(v_a_3599_);
lean_dec_ref(v_root_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_fns_u2082_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_lhs_3311_);
v_a_3614_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3605_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3605_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec(v_a_3601_);
lean_dec(v_a_3599_);
lean_dec_ref(v_root_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_fns_u2082_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_lhs_3311_);
v_a_3622_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3603_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3603_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
lean_dec(v_a_3599_);
lean_dec_ref(v_root_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_fns_u2082_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_lhs_3311_);
v_a_3630_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3600_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3600_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec_ref(v_root_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_fns_u2082_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_lhs_3311_);
v_a_3638_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3598_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3598_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_dec_ref(v_root_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_fns_u2082_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_lhs_3311_);
return v___x_3597_;
}
}
}
}
else
{
lean_dec_ref(v_root_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_fns_u2082_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_lhs_3311_);
return v___x_3591_;
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec_ref(v_fns_u2082_3572_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhs_3311_);
v_a_3646_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3588_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3588_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
v___jp_3654_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3669_ = lean_array_get_size(v___y_3657_);
v___x_3670_ = lean_unsigned_to_nat(0u);
v___x_3671_ = lean_nat_dec_eq(v___x_3669_, v___x_3670_);
if (v___x_3671_ == 0)
{
lean_object* v_self_3672_; lean_object* v___x_3673_; 
v_self_3672_ = lean_ctor_get(v_lhsRoot_3315_, 0);
lean_inc_ref(v_self_3672_);
v___x_3673_ = l_Lean_Meta_Grind_getFnRoots(v_self_3672_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v___y_3568_ = v___y_3655_;
v___y_3569_ = v___y_3656_;
v___y_3570_ = v_fns_u2081_3658_;
v___y_3571_ = v___y_3657_;
v_fns_u2082_3572_ = v_a_3674_;
v___y_3573_ = v___y_3659_;
v___y_3574_ = v___y_3660_;
v___y_3575_ = v___y_3661_;
v___y_3576_ = v___y_3662_;
v___y_3577_ = v___y_3663_;
v___y_3578_ = v___y_3664_;
v___y_3579_ = v___y_3665_;
v___y_3580_ = v___y_3666_;
v___y_3581_ = v___y_3667_;
v___y_3582_ = v___y_3668_;
goto v___jp_3567_;
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec_ref(v_fns_u2081_3658_);
lean_dec_ref(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhs_3311_);
v_a_3675_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3673_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3673_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v___x_3683_; 
v___x_3683_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3568_ = v___y_3655_;
v___y_3569_ = v___y_3656_;
v___y_3570_ = v_fns_u2081_3658_;
v___y_3571_ = v___y_3657_;
v_fns_u2082_3572_ = v___x_3683_;
v___y_3573_ = v___y_3659_;
v___y_3574_ = v___y_3660_;
v___y_3575_ = v___y_3661_;
v___y_3576_ = v___y_3662_;
v___y_3577_ = v___y_3663_;
v___y_3578_ = v___y_3664_;
v___y_3579_ = v___y_3665_;
v___y_3580_ = v___y_3666_;
v___y_3581_ = v___y_3667_;
v___y_3582_ = v___y_3668_;
goto v___jp_3567_;
}
}
v___jp_3684_:
{
lean_object* v___x_3695_; 
lean_inc_ref(v_lhs_3311_);
v___x_3695_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3311_, v___y_3685_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3762_; 
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v___x_3695_, 0);
lean_dec(v_unused_3763_);
v___x_3697_ = v___x_3695_;
v_isShared_3698_ = v_isSharedCheck_3762_;
goto v_resetjp_3696_;
}
else
{
lean_dec(v___x_3695_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3762_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v_self_3699_; lean_object* v_next_3700_; lean_object* v_root_3701_; lean_object* v_congr_3702_; lean_object* v_size_3703_; uint8_t v_interpreted_3704_; uint8_t v_ctor_3705_; uint8_t v_hasLambdas_3706_; uint8_t v_heqProofs_3707_; lean_object* v_idx_3708_; lean_object* v_generation_3709_; lean_object* v_mt_3710_; lean_object* v_sTerms_3711_; uint8_t v_funCC_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3759_; 
v_self_3699_ = lean_ctor_get(v_lhsNode_3313_, 0);
v_next_3700_ = lean_ctor_get(v_lhsNode_3313_, 1);
v_root_3701_ = lean_ctor_get(v_lhsNode_3313_, 2);
v_congr_3702_ = lean_ctor_get(v_lhsNode_3313_, 3);
v_size_3703_ = lean_ctor_get(v_lhsNode_3313_, 6);
v_interpreted_3704_ = lean_ctor_get_uint8(v_lhsNode_3313_, sizeof(void*)*11 + 1);
v_ctor_3705_ = lean_ctor_get_uint8(v_lhsNode_3313_, sizeof(void*)*11 + 2);
v_hasLambdas_3706_ = lean_ctor_get_uint8(v_lhsNode_3313_, sizeof(void*)*11 + 3);
v_heqProofs_3707_ = lean_ctor_get_uint8(v_lhsNode_3313_, sizeof(void*)*11 + 4);
v_idx_3708_ = lean_ctor_get(v_lhsNode_3313_, 7);
v_generation_3709_ = lean_ctor_get(v_lhsNode_3313_, 8);
v_mt_3710_ = lean_ctor_get(v_lhsNode_3313_, 9);
v_sTerms_3711_ = lean_ctor_get(v_lhsNode_3313_, 10);
v_funCC_3712_ = lean_ctor_get_uint8(v_lhsNode_3313_, sizeof(void*)*11 + 5);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_lhsNode_3313_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3760_ = lean_ctor_get(v_lhsNode_3313_, 5);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_lhsNode_3313_, 4);
lean_dec(v_unused_3761_);
v___x_3714_ = v_lhsNode_3313_;
v_isShared_3715_ = v_isSharedCheck_3759_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_sTerms_3711_);
lean_inc(v_mt_3710_);
lean_inc(v_generation_3709_);
lean_inc(v_idx_3708_);
lean_inc(v_size_3703_);
lean_inc(v_congr_3702_);
lean_inc(v_root_3701_);
lean_inc(v_next_3700_);
lean_inc(v_self_3699_);
lean_dec(v_lhsNode_3313_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3759_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set_tag(v___x_3697_, 1);
lean_ctor_set(v___x_3697_, 0, v_rhs_3312_);
v___x_3717_ = v___x_3697_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_rhs_3312_);
v___x_3717_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3718_, 0, v_proof_3309_);
lean_inc_ref(v_root_3701_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 5, v___x_3718_);
lean_ctor_set(v___x_3714_, 4, v___x_3717_);
v___x_3720_ = v___x_3714_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 11, 6);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_self_3699_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_next_3700_);
lean_ctor_set(v_reuseFailAlloc_3757_, 2, v_root_3701_);
lean_ctor_set(v_reuseFailAlloc_3757_, 3, v_congr_3702_);
lean_ctor_set(v_reuseFailAlloc_3757_, 4, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3757_, 5, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3757_, 6, v_size_3703_);
lean_ctor_set(v_reuseFailAlloc_3757_, 7, v_idx_3708_);
lean_ctor_set(v_reuseFailAlloc_3757_, 8, v_generation_3709_);
lean_ctor_set(v_reuseFailAlloc_3757_, 9, v_mt_3710_);
lean_ctor_set(v_reuseFailAlloc_3757_, 10, v_sTerms_3711_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*11 + 1, v_interpreted_3704_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*11 + 2, v_ctor_3705_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*11 + 3, v_hasLambdas_3706_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*11 + 4, v_heqProofs_3707_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*11 + 5, v_funCC_3712_);
v___x_3720_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; 
lean_ctor_set_uint8(v___x_3720_, sizeof(void*)*11, v_flipped_3317_);
lean_inc_ref(v_lhs_3311_);
v___x_3721_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3311_, v___x_3720_, v___y_3685_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v___x_3722_; 
lean_dec_ref(v___x_3721_);
v___x_3722_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3315_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3316_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref(v___x_3724_);
v___x_3726_ = lean_array_get_size(v_a_3723_);
v___x_3727_ = lean_unsigned_to_nat(0u);
v___x_3728_ = lean_nat_dec_eq(v___x_3726_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v_self_3729_; lean_object* v___x_3730_; 
v_self_3729_ = lean_ctor_get(v_rhsRoot_3316_, 0);
lean_inc_ref(v_self_3729_);
v___x_3730_ = l_Lean_Meta_Grind_getFnRoots(v_self_3729_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref(v___x_3730_);
v___y_3655_ = v_a_3723_;
v___y_3656_ = v_root_3701_;
v___y_3657_ = v_a_3725_;
v_fns_u2081_3658_ = v_a_3731_;
v___y_3659_ = v___y_3685_;
v___y_3660_ = v___y_3686_;
v___y_3661_ = v___y_3687_;
v___y_3662_ = v___y_3688_;
v___y_3663_ = v___y_3689_;
v___y_3664_ = v___y_3690_;
v___y_3665_ = v___y_3691_;
v___y_3666_ = v___y_3692_;
v___y_3667_ = v___y_3693_;
v___y_3668_ = v___y_3694_;
goto v___jp_3654_;
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v_a_3725_);
lean_dec(v_a_3723_);
lean_dec_ref(v_root_3701_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhs_3311_);
v_a_3732_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3730_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3730_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v___x_3740_; 
v___x_3740_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3655_ = v_a_3723_;
v___y_3656_ = v_root_3701_;
v___y_3657_ = v_a_3725_;
v_fns_u2081_3658_ = v___x_3740_;
v___y_3659_ = v___y_3685_;
v___y_3660_ = v___y_3686_;
v___y_3661_ = v___y_3687_;
v___y_3662_ = v___y_3688_;
v___y_3663_ = v___y_3689_;
v___y_3664_ = v___y_3690_;
v___y_3665_ = v___y_3691_;
v___y_3666_ = v___y_3692_;
v___y_3667_ = v___y_3693_;
v___y_3668_ = v___y_3694_;
goto v___jp_3654_;
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec(v_a_3723_);
lean_dec_ref(v_root_3701_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhs_3311_);
v_a_3741_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3724_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3724_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec_ref(v_root_3701_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhs_3311_);
v_a_3749_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3722_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3722_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
else
{
lean_dec_ref(v_root_3701_);
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhs_3311_);
return v___x_3721_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3316_);
lean_dec_ref(v_lhsRoot_3315_);
lean_dec_ref(v_rhsNode_3314_);
lean_dec_ref(v_lhsNode_3313_);
lean_dec_ref(v_rhs_3312_);
lean_dec_ref(v_lhs_3311_);
lean_dec_ref(v_proof_3309_);
return v___x_3695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3793_ = _args[0];
lean_object* v_isHEq_3794_ = _args[1];
lean_object* v_lhs_3795_ = _args[2];
lean_object* v_rhs_3796_ = _args[3];
lean_object* v_lhsNode_3797_ = _args[4];
lean_object* v_rhsNode_3798_ = _args[5];
lean_object* v_lhsRoot_3799_ = _args[6];
lean_object* v_rhsRoot_3800_ = _args[7];
lean_object* v_flipped_3801_ = _args[8];
lean_object* v_a_3802_ = _args[9];
lean_object* v_a_3803_ = _args[10];
lean_object* v_a_3804_ = _args[11];
lean_object* v_a_3805_ = _args[12];
lean_object* v_a_3806_ = _args[13];
lean_object* v_a_3807_ = _args[14];
lean_object* v_a_3808_ = _args[15];
lean_object* v_a_3809_ = _args[16];
lean_object* v_a_3810_ = _args[17];
lean_object* v_a_3811_ = _args[18];
lean_object* v_a_3812_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3813_; uint8_t v_flipped_boxed_3814_; lean_object* v_res_3815_; 
v_isHEq_boxed_3813_ = lean_unbox(v_isHEq_3794_);
v_flipped_boxed_3814_ = lean_unbox(v_flipped_3801_);
v_res_3815_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3793_, v_isHEq_boxed_3813_, v_lhs_3795_, v_rhs_3796_, v_lhsNode_3797_, v_rhsNode_3798_, v_lhsRoot_3799_, v_rhsRoot_3800_, v_flipped_boxed_3814_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3806_);
lean_dec(v_a_3805_);
lean_dec_ref(v_a_3804_);
lean_dec(v_a_3803_);
lean_dec(v_a_3802_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3816_, lean_object* v_as_x27_3817_, lean_object* v_b_3818_, lean_object* v_a_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3817_, v_b_3818_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3832_, lean_object* v_as_x27_3833_, lean_object* v_b_3834_, lean_object* v_a_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3832_, v_as_x27_3833_, v_b_3834_, v_a_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec(v_as_3832_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3848_, lean_object* v_as_x27_3849_, lean_object* v_b_3850_, lean_object* v_a_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3849_, v_b_3850_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3864_, lean_object* v_as_x27_3865_, lean_object* v_b_3866_, lean_object* v_a_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3864_, v_as_x27_3865_, v_b_3866_, v_a_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec(v_as_3864_);
return v_res_3879_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_3882_ = l_Lean_stringToMessageData(v___x_3881_);
return v___x_3882_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_3888_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3889_ = l_Lean_Name_append(v___x_3888_, v___x_3887_);
return v___x_3889_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_3892_ = l_Lean_stringToMessageData(v___x_3891_);
return v___x_3892_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_3895_ = l_Lean_stringToMessageData(v___x_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_3896_, lean_object* v_rhs_3897_, lean_object* v_proof_3898_, uint8_t v_isHEq_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = lean_st_ref_get(v_a_3900_);
lean_inc_ref(v_lhs_3896_);
v___x_3915_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3914_, v_lhs_3896_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref(v___x_3915_);
v___x_3917_ = lean_st_ref_get(v_a_3900_);
lean_inc_ref(v_rhs_3897_);
v___x_3918_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3917_, v_rhs_3897_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v_root_3920_; lean_object* v_root_3921_; uint8_t v___x_3922_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref(v___x_3918_);
v_root_3920_ = lean_ctor_get(v_a_3916_, 2);
v_root_3921_ = lean_ctor_get(v_a_3919_, 2);
v___x_3922_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_3920_, v_root_3921_);
if (v___x_3922_ == 0)
{
lean_object* v_options_3923_; lean_object* v_inheritedTraceOptions_3924_; uint8_t v_hasTrace_3925_; uint8_t v___x_3926_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3963_; lean_object* v___y_3964_; uint8_t v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; uint8_t v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; uint8_t v___y_4004_; lean_object* v___y_4009_; lean_object* v___y_4010_; uint8_t v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4036_; uint8_t v___y_4037_; lean_object* v___y_4038_; uint8_t v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; uint8_t v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; uint8_t v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; uint8_t v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; uint8_t v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; uint8_t v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; uint8_t v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; uint8_t v___y_4098_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v_size_4103_; uint8_t v_interpreted_4104_; uint8_t v_ctor_4105_; uint8_t v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v_size_4114_; uint8_t v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; uint8_t v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; uint8_t v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; uint8_t v___y_4134_; lean_object* v___y_4145_; uint8_t v_interpreted_4146_; lean_object* v___y_4147_; uint8_t v_valueInconsistency_4148_; uint8_t v_trueEqFalse_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4162_; lean_object* v___y_4163_; uint8_t v_valueInconsistency_4164_; uint8_t v_trueEqFalse_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; uint8_t v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; uint8_t v___y_4232_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; 
v_options_3923_ = lean_ctor_get(v_a_3908_, 2);
v_inheritedTraceOptions_3924_ = lean_ctor_get(v_a_3908_, 13);
v_hasTrace_3925_ = lean_ctor_get_uint8(v_options_3923_, sizeof(void*)*1);
v___x_3926_ = 1;
if (v_hasTrace_3925_ == 0)
{
v___y_4239_ = v_a_3900_;
v___y_4240_ = v_a_3901_;
v___y_4241_ = v_a_3902_;
v___y_4242_ = v_a_3903_;
v___y_4243_ = v_a_3904_;
v___y_4244_ = v_a_3905_;
v___y_4245_ = v_a_3906_;
v___y_4246_ = v_a_3907_;
v___y_4247_ = v_a_3908_;
v___y_4248_ = v_a_3909_;
goto v___jp_4238_;
}
else
{
lean_object* v___x_4274_; lean_object* v___y_4276_; lean_object* v___x_4288_; uint8_t v___x_4289_; 
v___x_4274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4289_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3924_, v_options_3923_, v___x_4288_);
if (v___x_4289_ == 0)
{
v___y_4239_ = v_a_3900_;
v___y_4240_ = v_a_3901_;
v___y_4241_ = v_a_3902_;
v___y_4242_ = v_a_3903_;
v___y_4243_ = v_a_3904_;
v___y_4244_ = v_a_3905_;
v___y_4245_ = v_a_3906_;
v___y_4246_ = v_a_3907_;
v___y_4247_ = v_a_3908_;
v___y_4248_ = v_a_3909_;
goto v___jp_4238_;
}
else
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Lean_Meta_Grind_updateLastTag(v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_dec_ref(v___x_4290_);
if (v_isHEq_3899_ == 0)
{
lean_object* v___x_4291_; 
lean_inc_ref(v_rhs_3897_);
lean_inc_ref(v_lhs_3896_);
v___x_4291_ = l_Lean_Meta_mkEq(v_lhs_3896_, v_rhs_3897_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
v___y_4276_ = v___x_4291_;
goto v___jp_4275_;
}
else
{
lean_object* v___x_4292_; 
lean_inc_ref(v_rhs_3897_);
lean_inc_ref(v_lhs_3896_);
v___x_4292_ = l_Lean_Meta_mkHEq(v_lhs_3896_, v_rhs_3897_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
v___y_4276_ = v___x_4292_;
goto v___jp_4275_;
}
}
else
{
lean_dec(v_a_3919_);
lean_dec(v_a_3916_);
lean_dec_ref(v_proof_3898_);
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
return v___x_4290_;
}
}
v___jp_4275_:
{
if (lean_obj_tag(v___y_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v_a_4277_ = lean_ctor_get(v___y_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref(v___y_4276_);
v___x_4278_ = l_Lean_MessageData_ofExpr(v_a_4277_);
v___x_4279_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4274_, v___x_4278_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_dec_ref(v___x_4279_);
v___y_4239_ = v_a_3900_;
v___y_4240_ = v_a_3901_;
v___y_4241_ = v_a_3902_;
v___y_4242_ = v_a_3903_;
v___y_4243_ = v_a_3904_;
v___y_4244_ = v_a_3905_;
v___y_4245_ = v_a_3906_;
v___y_4246_ = v_a_3907_;
v___y_4247_ = v_a_3908_;
v___y_4248_ = v_a_3909_;
goto v___jp_4238_;
}
else
{
lean_dec(v_a_3919_);
lean_dec(v_a_3916_);
lean_dec_ref(v_proof_3898_);
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
return v___x_4279_;
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec(v_a_3919_);
lean_dec(v_a_3916_);
lean_dec_ref(v_proof_3898_);
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
v_a_4280_ = lean_ctor_get(v___y_4276_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___y_4276_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___y_4276_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___y_4276_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
}
v___jp_3927_:
{
lean_object* v_options_3938_; uint8_t v_hasTrace_3939_; 
v_options_3938_ = lean_ctor_get(v___y_3936_, 2);
v_hasTrace_3939_ = lean_ctor_get_uint8(v_options_3938_, sizeof(void*)*1);
if (v_hasTrace_3939_ == 0)
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Lean_Meta_Grind_checkInvariants(v___x_3922_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
return v___x_3940_;
}
else
{
lean_object* v_inheritedTraceOptions_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; 
v_inheritedTraceOptions_3941_ = lean_ctor_get(v___y_3936_, 13);
v___x_3942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3944_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3941_, v_options_3938_, v___x_3943_);
if (v___x_3944_ == 0)
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_Meta_Grind_checkInvariants(v___x_3922_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
return v___x_3945_;
}
else
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_Meta_Grind_updateLastTag(v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
lean_dec_ref(v___x_3946_);
v___x_3947_ = lean_st_ref_get(v___y_3928_);
v___x_3948_ = l_Lean_Meta_Grind_Goal_ppState(v___x_3947_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_object* v_a_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc(v_a_3949_);
lean_dec_ref(v___x_3948_);
v___x_3950_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_3951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
lean_ctor_set(v___x_3951_, 1, v_a_3949_);
v___x_3952_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_3942_, v___x_3951_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v___x_3953_; 
lean_dec_ref(v___x_3952_);
v___x_3953_ = l_Lean_Meta_Grind_checkInvariants(v___x_3922_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
return v___x_3953_;
}
else
{
return v___x_3952_;
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
v_a_3954_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3948_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3948_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
return v___x_3946_;
}
}
}
}
v___jp_3962_:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3966_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; uint8_t v___x_3978_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref(v___x_3976_);
v___x_3978_ = lean_unbox(v_a_3977_);
lean_dec(v_a_3977_);
if (v___x_3978_ == 0)
{
if (v___y_3965_ == 0)
{
lean_dec_ref(v___y_3964_);
lean_dec_ref(v___y_3963_);
v___y_3928_ = v___y_3966_;
v___y_3929_ = v___y_3967_;
v___y_3930_ = v___y_3968_;
v___y_3931_ = v___y_3969_;
v___y_3932_ = v___y_3970_;
v___y_3933_ = v___y_3971_;
v___y_3934_ = v___y_3972_;
v___y_3935_ = v___y_3973_;
v___y_3936_ = v___y_3974_;
v___y_3937_ = v___y_3975_;
goto v___jp_3927_;
}
else
{
lean_object* v_self_3979_; lean_object* v_self_3980_; lean_object* v___x_3981_; 
v_self_3979_ = lean_ctor_get(v___y_3963_, 0);
lean_inc_ref(v_self_3979_);
lean_dec_ref(v___y_3963_);
v_self_3980_ = lean_ctor_get(v___y_3964_, 0);
lean_inc_ref(v_self_3980_);
lean_dec_ref(v___y_3964_);
v___x_3981_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_3979_, v_self_3980_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_dec_ref(v___x_3981_);
v___y_3928_ = v___y_3966_;
v___y_3929_ = v___y_3967_;
v___y_3930_ = v___y_3968_;
v___y_3931_ = v___y_3969_;
v___y_3932_ = v___y_3970_;
v___y_3933_ = v___y_3971_;
v___y_3934_ = v___y_3972_;
v___y_3935_ = v___y_3973_;
v___y_3936_ = v___y_3974_;
v___y_3937_ = v___y_3975_;
goto v___jp_3927_;
}
else
{
return v___x_3981_;
}
}
}
else
{
lean_dec_ref(v___y_3964_);
lean_dec_ref(v___y_3963_);
v___y_3928_ = v___y_3966_;
v___y_3929_ = v___y_3967_;
v___y_3930_ = v___y_3968_;
v___y_3931_ = v___y_3969_;
v___y_3932_ = v___y_3970_;
v___y_3933_ = v___y_3971_;
v___y_3934_ = v___y_3972_;
v___y_3935_ = v___y_3973_;
v___y_3936_ = v___y_3974_;
v___y_3937_ = v___y_3975_;
goto v___jp_3927_;
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v___y_3964_);
lean_dec_ref(v___y_3963_);
v_a_3982_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3976_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3976_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
v___jp_3990_:
{
if (v___y_4004_ == 0)
{
v___y_3963_ = v___y_4001_;
v___y_3964_ = v___y_3997_;
v___y_3965_ = v___y_3998_;
v___y_3966_ = v___y_3999_;
v___y_3967_ = v___y_3992_;
v___y_3968_ = v___y_3991_;
v___y_3969_ = v___y_4000_;
v___y_3970_ = v___y_3993_;
v___y_3971_ = v___y_4003_;
v___y_3972_ = v___y_3994_;
v___y_3973_ = v___y_3996_;
v___y_3974_ = v___y_3995_;
v___y_3975_ = v___y_4002_;
goto v___jp_3962_;
}
else
{
lean_object* v_self_4005_; lean_object* v_self_4006_; lean_object* v___x_4007_; 
v_self_4005_ = lean_ctor_get(v___y_4001_, 0);
v_self_4006_ = lean_ctor_get(v___y_3997_, 0);
lean_inc_ref(v_self_4006_);
lean_inc_ref(v_self_4005_);
v___x_4007_ = l_Lean_Meta_Grind_propagateCtor(v_self_4005_, v_self_4006_, v___y_3999_, v___y_3992_, v___y_3991_, v___y_4000_, v___y_3993_, v___y_4003_, v___y_3994_, v___y_3996_, v___y_3995_, v___y_4002_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_dec_ref(v___x_4007_);
v___y_3963_ = v___y_4001_;
v___y_3964_ = v___y_3997_;
v___y_3965_ = v___y_3998_;
v___y_3966_ = v___y_3999_;
v___y_3967_ = v___y_3992_;
v___y_3968_ = v___y_3991_;
v___y_3969_ = v___y_4000_;
v___y_3970_ = v___y_3993_;
v___y_3971_ = v___y_4003_;
v___y_3972_ = v___y_3994_;
v___y_3973_ = v___y_3996_;
v___y_3974_ = v___y_3995_;
v___y_3975_ = v___y_4002_;
goto v___jp_3962_;
}
else
{
lean_dec_ref(v___y_4001_);
lean_dec_ref(v___y_3997_);
return v___x_4007_;
}
}
}
v___jp_4008_:
{
lean_object* v___x_4022_; 
v___x_4022_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4012_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; uint8_t v___x_4024_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_a_4023_);
lean_dec_ref(v___x_4022_);
v___x_4024_ = lean_unbox(v_a_4023_);
lean_dec(v_a_4023_);
if (v___x_4024_ == 0)
{
uint8_t v_ctor_4025_; 
v_ctor_4025_ = lean_ctor_get_uint8(v___y_4009_, sizeof(void*)*11 + 2);
if (v_ctor_4025_ == 0)
{
v___y_3991_ = v___y_4014_;
v___y_3992_ = v___y_4013_;
v___y_3993_ = v___y_4016_;
v___y_3994_ = v___y_4018_;
v___y_3995_ = v___y_4020_;
v___y_3996_ = v___y_4019_;
v___y_3997_ = v___y_4010_;
v___y_3998_ = v___y_4011_;
v___y_3999_ = v___y_4012_;
v___y_4000_ = v___y_4015_;
v___y_4001_ = v___y_4009_;
v___y_4002_ = v___y_4021_;
v___y_4003_ = v___y_4017_;
v___y_4004_ = v___x_3922_;
goto v___jp_3990_;
}
else
{
uint8_t v_ctor_4026_; 
v_ctor_4026_ = lean_ctor_get_uint8(v___y_4010_, sizeof(void*)*11 + 2);
v___y_3991_ = v___y_4014_;
v___y_3992_ = v___y_4013_;
v___y_3993_ = v___y_4016_;
v___y_3994_ = v___y_4018_;
v___y_3995_ = v___y_4020_;
v___y_3996_ = v___y_4019_;
v___y_3997_ = v___y_4010_;
v___y_3998_ = v___y_4011_;
v___y_3999_ = v___y_4012_;
v___y_4000_ = v___y_4015_;
v___y_4001_ = v___y_4009_;
v___y_4002_ = v___y_4021_;
v___y_4003_ = v___y_4017_;
v___y_4004_ = v_ctor_4026_;
goto v___jp_3990_;
}
}
else
{
v___y_3963_ = v___y_4009_;
v___y_3964_ = v___y_4010_;
v___y_3965_ = v___y_4011_;
v___y_3966_ = v___y_4012_;
v___y_3967_ = v___y_4013_;
v___y_3968_ = v___y_4014_;
v___y_3969_ = v___y_4015_;
v___y_3970_ = v___y_4016_;
v___y_3971_ = v___y_4017_;
v___y_3972_ = v___y_4018_;
v___y_3973_ = v___y_4019_;
v___y_3974_ = v___y_4020_;
v___y_3975_ = v___y_4021_;
goto v___jp_3962_;
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec_ref(v___y_4010_);
lean_dec_ref(v___y_4009_);
v_a_4027_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_4022_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4022_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
v___jp_4035_:
{
if (v___y_4037_ == 0)
{
v___y_4009_ = v___y_4036_;
v___y_4010_ = v___y_4038_;
v___y_4011_ = v___y_4039_;
v___y_4012_ = v___y_4040_;
v___y_4013_ = v___y_4041_;
v___y_4014_ = v___y_4042_;
v___y_4015_ = v___y_4043_;
v___y_4016_ = v___y_4044_;
v___y_4017_ = v___y_4045_;
v___y_4018_ = v___y_4046_;
v___y_4019_ = v___y_4047_;
v___y_4020_ = v___y_4048_;
v___y_4021_ = v___y_4049_;
goto v___jp_4008_;
}
else
{
lean_object* v___x_4050_; 
v___x_4050_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_dec_ref(v___x_4050_);
v___y_4009_ = v___y_4036_;
v___y_4010_ = v___y_4038_;
v___y_4011_ = v___y_4039_;
v___y_4012_ = v___y_4040_;
v___y_4013_ = v___y_4041_;
v___y_4014_ = v___y_4042_;
v___y_4015_ = v___y_4043_;
v___y_4016_ = v___y_4044_;
v___y_4017_ = v___y_4045_;
v___y_4018_ = v___y_4046_;
v___y_4019_ = v___y_4047_;
v___y_4020_ = v___y_4048_;
v___y_4021_ = v___y_4049_;
goto v___jp_4008_;
}
else
{
lean_dec_ref(v___y_4038_);
lean_dec_ref(v___y_4036_);
return v___x_4050_;
}
}
}
v___jp_4051_:
{
lean_object* v___x_4066_; 
lean_inc_ref(v___y_4062_);
lean_inc_ref(v___y_4054_);
v___x_4066_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3898_, v_isHEq_3899_, v_rhs_3897_, v_lhs_3896_, v_a_3919_, v_a_3916_, v___y_4054_, v___y_4062_, v___x_3926_, v___y_4056_, v___y_4053_, v___y_4065_, v___y_4057_, v___y_4052_, v___y_4058_, v___y_4059_, v___y_4064_, v___y_4061_, v___y_4060_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_dec_ref(v___x_4066_);
v___y_4036_ = v___y_4062_;
v___y_4037_ = v___y_4063_;
v___y_4038_ = v___y_4054_;
v___y_4039_ = v___y_4055_;
v___y_4040_ = v___y_4056_;
v___y_4041_ = v___y_4053_;
v___y_4042_ = v___y_4065_;
v___y_4043_ = v___y_4057_;
v___y_4044_ = v___y_4052_;
v___y_4045_ = v___y_4058_;
v___y_4046_ = v___y_4059_;
v___y_4047_ = v___y_4064_;
v___y_4048_ = v___y_4061_;
v___y_4049_ = v___y_4060_;
goto v___jp_4035_;
}
else
{
lean_dec_ref(v___y_4062_);
lean_dec_ref(v___y_4054_);
return v___x_4066_;
}
}
v___jp_4067_:
{
lean_object* v___x_4082_; 
lean_inc_ref(v___y_4070_);
lean_inc_ref(v___y_4078_);
v___x_4082_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3898_, v_isHEq_3899_, v_lhs_3896_, v_rhs_3897_, v_a_3916_, v_a_3919_, v___y_4078_, v___y_4070_, v___x_3922_, v___y_4072_, v___y_4069_, v___y_4081_, v___y_4073_, v___y_4068_, v___y_4074_, v___y_4075_, v___y_4080_, v___y_4077_, v___y_4076_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_dec_ref(v___x_4082_);
v___y_4036_ = v___y_4078_;
v___y_4037_ = v___y_4079_;
v___y_4038_ = v___y_4070_;
v___y_4039_ = v___y_4071_;
v___y_4040_ = v___y_4072_;
v___y_4041_ = v___y_4069_;
v___y_4042_ = v___y_4081_;
v___y_4043_ = v___y_4073_;
v___y_4044_ = v___y_4068_;
v___y_4045_ = v___y_4074_;
v___y_4046_ = v___y_4075_;
v___y_4047_ = v___y_4080_;
v___y_4048_ = v___y_4077_;
v___y_4049_ = v___y_4076_;
goto v___jp_4035_;
}
else
{
lean_dec_ref(v___y_4078_);
lean_dec_ref(v___y_4070_);
return v___x_4082_;
}
}
v___jp_4083_:
{
if (v___y_4098_ == 0)
{
v___y_4068_ = v___y_4084_;
v___y_4069_ = v___y_4085_;
v___y_4070_ = v___y_4086_;
v___y_4071_ = v___y_4087_;
v___y_4072_ = v___y_4088_;
v___y_4073_ = v___y_4089_;
v___y_4074_ = v___y_4090_;
v___y_4075_ = v___y_4091_;
v___y_4076_ = v___y_4092_;
v___y_4077_ = v___y_4093_;
v___y_4078_ = v___y_4094_;
v___y_4079_ = v___y_4095_;
v___y_4080_ = v___y_4096_;
v___y_4081_ = v___y_4097_;
goto v___jp_4067_;
}
else
{
v___y_4052_ = v___y_4084_;
v___y_4053_ = v___y_4085_;
v___y_4054_ = v___y_4086_;
v___y_4055_ = v___y_4087_;
v___y_4056_ = v___y_4088_;
v___y_4057_ = v___y_4089_;
v___y_4058_ = v___y_4090_;
v___y_4059_ = v___y_4091_;
v___y_4060_ = v___y_4092_;
v___y_4061_ = v___y_4093_;
v___y_4062_ = v___y_4094_;
v___y_4063_ = v___y_4095_;
v___y_4064_ = v___y_4096_;
v___y_4065_ = v___y_4097_;
goto v___jp_4051_;
}
}
v___jp_4099_:
{
uint8_t v___x_4118_; 
v___x_4118_ = lean_nat_dec_lt(v_size_4103_, v_size_4114_);
lean_dec(v_size_4114_);
lean_dec(v_size_4103_);
if (v___x_4118_ == 0)
{
v___y_4084_ = v___y_4100_;
v___y_4085_ = v___y_4101_;
v___y_4086_ = v___y_4102_;
v___y_4087_ = v___y_4106_;
v___y_4088_ = v___y_4107_;
v___y_4089_ = v___y_4108_;
v___y_4090_ = v___y_4109_;
v___y_4091_ = v___y_4110_;
v___y_4092_ = v___y_4111_;
v___y_4093_ = v___y_4112_;
v___y_4094_ = v___y_4113_;
v___y_4095_ = v___y_4115_;
v___y_4096_ = v___y_4116_;
v___y_4097_ = v___y_4117_;
v___y_4098_ = v___x_3922_;
goto v___jp_4083_;
}
else
{
if (v_interpreted_4104_ == 0)
{
if (v___x_4118_ == 0)
{
v___y_4084_ = v___y_4100_;
v___y_4085_ = v___y_4101_;
v___y_4086_ = v___y_4102_;
v___y_4087_ = v___y_4106_;
v___y_4088_ = v___y_4107_;
v___y_4089_ = v___y_4108_;
v___y_4090_ = v___y_4109_;
v___y_4091_ = v___y_4110_;
v___y_4092_ = v___y_4111_;
v___y_4093_ = v___y_4112_;
v___y_4094_ = v___y_4113_;
v___y_4095_ = v___y_4115_;
v___y_4096_ = v___y_4116_;
v___y_4097_ = v___y_4117_;
v___y_4098_ = v___x_3922_;
goto v___jp_4083_;
}
else
{
if (v_ctor_4105_ == 0)
{
v___y_4084_ = v___y_4100_;
v___y_4085_ = v___y_4101_;
v___y_4086_ = v___y_4102_;
v___y_4087_ = v___y_4106_;
v___y_4088_ = v___y_4107_;
v___y_4089_ = v___y_4108_;
v___y_4090_ = v___y_4109_;
v___y_4091_ = v___y_4110_;
v___y_4092_ = v___y_4111_;
v___y_4093_ = v___y_4112_;
v___y_4094_ = v___y_4113_;
v___y_4095_ = v___y_4115_;
v___y_4096_ = v___y_4116_;
v___y_4097_ = v___y_4117_;
v___y_4098_ = v___x_4118_;
goto v___jp_4083_;
}
else
{
v___y_4068_ = v___y_4100_;
v___y_4069_ = v___y_4101_;
v___y_4070_ = v___y_4102_;
v___y_4071_ = v___y_4106_;
v___y_4072_ = v___y_4107_;
v___y_4073_ = v___y_4108_;
v___y_4074_ = v___y_4109_;
v___y_4075_ = v___y_4110_;
v___y_4076_ = v___y_4111_;
v___y_4077_ = v___y_4112_;
v___y_4078_ = v___y_4113_;
v___y_4079_ = v___y_4115_;
v___y_4080_ = v___y_4116_;
v___y_4081_ = v___y_4117_;
goto v___jp_4067_;
}
}
}
else
{
v___y_4084_ = v___y_4100_;
v___y_4085_ = v___y_4101_;
v___y_4086_ = v___y_4102_;
v___y_4087_ = v___y_4106_;
v___y_4088_ = v___y_4107_;
v___y_4089_ = v___y_4108_;
v___y_4090_ = v___y_4109_;
v___y_4091_ = v___y_4110_;
v___y_4092_ = v___y_4111_;
v___y_4093_ = v___y_4112_;
v___y_4094_ = v___y_4113_;
v___y_4095_ = v___y_4115_;
v___y_4096_ = v___y_4116_;
v___y_4097_ = v___y_4117_;
v___y_4098_ = v___x_3922_;
goto v___jp_4083_;
}
}
}
v___jp_4119_:
{
if (v___y_4134_ == 0)
{
uint8_t v_ctor_4135_; 
v_ctor_4135_ = lean_ctor_get_uint8(v___y_4130_, sizeof(void*)*11 + 2);
if (v_ctor_4135_ == 0)
{
if (v___x_3922_ == 0)
{
lean_object* v_size_4136_; lean_object* v_size_4137_; uint8_t v_interpreted_4138_; uint8_t v_ctor_4139_; 
v_size_4136_ = lean_ctor_get(v___y_4130_, 6);
lean_inc(v_size_4136_);
v_size_4137_ = lean_ctor_get(v___y_4122_, 6);
lean_inc(v_size_4137_);
v_interpreted_4138_ = lean_ctor_get_uint8(v___y_4122_, sizeof(void*)*11 + 1);
v_ctor_4139_ = lean_ctor_get_uint8(v___y_4122_, sizeof(void*)*11 + 2);
v___y_4100_ = v___y_4120_;
v___y_4101_ = v___y_4121_;
v___y_4102_ = v___y_4122_;
v_size_4103_ = v_size_4137_;
v_interpreted_4104_ = v_interpreted_4138_;
v_ctor_4105_ = v_ctor_4139_;
v___y_4106_ = v___y_4123_;
v___y_4107_ = v___y_4124_;
v___y_4108_ = v___y_4125_;
v___y_4109_ = v___y_4126_;
v___y_4110_ = v___y_4127_;
v___y_4111_ = v___y_4128_;
v___y_4112_ = v___y_4129_;
v___y_4113_ = v___y_4130_;
v_size_4114_ = v_size_4136_;
v___y_4115_ = v___y_4131_;
v___y_4116_ = v___y_4132_;
v___y_4117_ = v___y_4133_;
goto v___jp_4099_;
}
else
{
v___y_4052_ = v___y_4120_;
v___y_4053_ = v___y_4121_;
v___y_4054_ = v___y_4122_;
v___y_4055_ = v___y_4123_;
v___y_4056_ = v___y_4124_;
v___y_4057_ = v___y_4125_;
v___y_4058_ = v___y_4126_;
v___y_4059_ = v___y_4127_;
v___y_4060_ = v___y_4128_;
v___y_4061_ = v___y_4129_;
v___y_4062_ = v___y_4130_;
v___y_4063_ = v___y_4131_;
v___y_4064_ = v___y_4132_;
v___y_4065_ = v___y_4133_;
goto v___jp_4051_;
}
}
else
{
uint8_t v_ctor_4140_; 
v_ctor_4140_ = lean_ctor_get_uint8(v___y_4122_, sizeof(void*)*11 + 2);
if (v_ctor_4140_ == 0)
{
v___y_4052_ = v___y_4120_;
v___y_4053_ = v___y_4121_;
v___y_4054_ = v___y_4122_;
v___y_4055_ = v___y_4123_;
v___y_4056_ = v___y_4124_;
v___y_4057_ = v___y_4125_;
v___y_4058_ = v___y_4126_;
v___y_4059_ = v___y_4127_;
v___y_4060_ = v___y_4128_;
v___y_4061_ = v___y_4129_;
v___y_4062_ = v___y_4130_;
v___y_4063_ = v___y_4131_;
v___y_4064_ = v___y_4132_;
v___y_4065_ = v___y_4133_;
goto v___jp_4051_;
}
else
{
lean_object* v_size_4141_; lean_object* v_size_4142_; uint8_t v_interpreted_4143_; 
v_size_4141_ = lean_ctor_get(v___y_4130_, 6);
lean_inc(v_size_4141_);
v_size_4142_ = lean_ctor_get(v___y_4122_, 6);
lean_inc(v_size_4142_);
v_interpreted_4143_ = lean_ctor_get_uint8(v___y_4122_, sizeof(void*)*11 + 1);
v___y_4100_ = v___y_4120_;
v___y_4101_ = v___y_4121_;
v___y_4102_ = v___y_4122_;
v_size_4103_ = v_size_4142_;
v_interpreted_4104_ = v_interpreted_4143_;
v_ctor_4105_ = v_ctor_4140_;
v___y_4106_ = v___y_4123_;
v___y_4107_ = v___y_4124_;
v___y_4108_ = v___y_4125_;
v___y_4109_ = v___y_4126_;
v___y_4110_ = v___y_4127_;
v___y_4111_ = v___y_4128_;
v___y_4112_ = v___y_4129_;
v___y_4113_ = v___y_4130_;
v_size_4114_ = v_size_4141_;
v___y_4115_ = v___y_4131_;
v___y_4116_ = v___y_4132_;
v___y_4117_ = v___y_4133_;
goto v___jp_4099_;
}
}
}
else
{
v___y_4052_ = v___y_4120_;
v___y_4053_ = v___y_4121_;
v___y_4054_ = v___y_4122_;
v___y_4055_ = v___y_4123_;
v___y_4056_ = v___y_4124_;
v___y_4057_ = v___y_4125_;
v___y_4058_ = v___y_4126_;
v___y_4059_ = v___y_4127_;
v___y_4060_ = v___y_4128_;
v___y_4061_ = v___y_4129_;
v___y_4062_ = v___y_4130_;
v___y_4063_ = v___y_4131_;
v___y_4064_ = v___y_4132_;
v___y_4065_ = v___y_4133_;
goto v___jp_4051_;
}
}
v___jp_4144_:
{
if (v_interpreted_4146_ == 0)
{
v___y_4120_ = v___y_4154_;
v___y_4121_ = v___y_4151_;
v___y_4122_ = v___y_4147_;
v___y_4123_ = v_valueInconsistency_4148_;
v___y_4124_ = v___y_4150_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4155_;
v___y_4127_ = v___y_4156_;
v___y_4128_ = v___y_4159_;
v___y_4129_ = v___y_4158_;
v___y_4130_ = v___y_4145_;
v___y_4131_ = v_trueEqFalse_4149_;
v___y_4132_ = v___y_4157_;
v___y_4133_ = v___y_4152_;
v___y_4134_ = v___x_3922_;
goto v___jp_4119_;
}
else
{
uint8_t v_interpreted_4160_; 
v_interpreted_4160_ = lean_ctor_get_uint8(v___y_4147_, sizeof(void*)*11 + 1);
if (v_interpreted_4160_ == 0)
{
v___y_4052_ = v___y_4154_;
v___y_4053_ = v___y_4151_;
v___y_4054_ = v___y_4147_;
v___y_4055_ = v_valueInconsistency_4148_;
v___y_4056_ = v___y_4150_;
v___y_4057_ = v___y_4153_;
v___y_4058_ = v___y_4155_;
v___y_4059_ = v___y_4156_;
v___y_4060_ = v___y_4159_;
v___y_4061_ = v___y_4158_;
v___y_4062_ = v___y_4145_;
v___y_4063_ = v_trueEqFalse_4149_;
v___y_4064_ = v___y_4157_;
v___y_4065_ = v___y_4152_;
goto v___jp_4051_;
}
else
{
v___y_4120_ = v___y_4154_;
v___y_4121_ = v___y_4151_;
v___y_4122_ = v___y_4147_;
v___y_4123_ = v_valueInconsistency_4148_;
v___y_4124_ = v___y_4150_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4155_;
v___y_4127_ = v___y_4156_;
v___y_4128_ = v___y_4159_;
v___y_4129_ = v___y_4158_;
v___y_4130_ = v___y_4145_;
v___y_4131_ = v_trueEqFalse_4149_;
v___y_4132_ = v___y_4157_;
v___y_4133_ = v___y_4152_;
v___y_4134_ = v___x_3922_;
goto v___jp_4119_;
}
}
}
v___jp_4161_:
{
uint8_t v_interpreted_4176_; 
v_interpreted_4176_ = lean_ctor_get_uint8(v___y_4162_, sizeof(void*)*11 + 1);
v___y_4145_ = v___y_4162_;
v_interpreted_4146_ = v_interpreted_4176_;
v___y_4147_ = v___y_4163_;
v_valueInconsistency_4148_ = v_valueInconsistency_4164_;
v_trueEqFalse_4149_ = v_trueEqFalse_4165_;
v___y_4150_ = v___y_4166_;
v___y_4151_ = v___y_4167_;
v___y_4152_ = v___y_4168_;
v___y_4153_ = v___y_4169_;
v___y_4154_ = v___y_4170_;
v___y_4155_ = v___y_4171_;
v___y_4156_ = v___y_4172_;
v___y_4157_ = v___y_4173_;
v___y_4158_ = v___y_4174_;
v___y_4159_ = v___y_4175_;
goto v___jp_4144_;
}
v___jp_4177_:
{
lean_object* v___x_4190_; 
v___x_4190_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4183_, v___y_4187_, v___y_4184_, v___y_4180_, v___y_4181_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_dec_ref(v___x_4190_);
v___y_4162_ = v___y_4189_;
v___y_4163_ = v___y_4186_;
v_valueInconsistency_4164_ = v___x_3922_;
v_trueEqFalse_4165_ = v___x_3926_;
v___y_4166_ = v___y_4183_;
v___y_4167_ = v___y_4182_;
v___y_4168_ = v___y_4188_;
v___y_4169_ = v___y_4185_;
v___y_4170_ = v___y_4178_;
v___y_4171_ = v___y_4179_;
v___y_4172_ = v___y_4187_;
v___y_4173_ = v___y_4184_;
v___y_4174_ = v___y_4180_;
v___y_4175_ = v___y_4181_;
goto v___jp_4161_;
}
else
{
lean_dec_ref(v___y_4189_);
lean_dec_ref(v___y_4186_);
lean_dec(v_a_3919_);
lean_dec(v_a_3916_);
lean_dec_ref(v_proof_3898_);
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
return v___x_4190_;
}
}
v___jp_4191_:
{
if (v___y_4199_ == 0)
{
lean_object* v_self_4205_; uint8_t v_interpreted_4206_; lean_object* v_self_4207_; lean_object* v___x_4208_; 
v_self_4205_ = lean_ctor_get(v___y_4202_, 0);
v_interpreted_4206_ = lean_ctor_get_uint8(v___y_4202_, sizeof(void*)*11 + 1);
v_self_4207_ = lean_ctor_get(v___y_4200_, 0);
lean_inc_ref(v_self_4207_);
lean_inc_ref(v_self_4205_);
v___x_4208_ = l_Lean_Meta_Grind_hasSameType(v_self_4205_, v_self_4207_, v___y_4203_, v___y_4198_, v___y_4194_, v___y_4195_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; uint8_t v___x_4210_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref(v___x_4208_);
v___x_4210_ = lean_unbox(v_a_4209_);
lean_dec(v_a_4209_);
if (v___x_4210_ == 0)
{
v___y_4145_ = v___y_4202_;
v_interpreted_4146_ = v_interpreted_4206_;
v___y_4147_ = v___y_4200_;
v_valueInconsistency_4148_ = v___x_3922_;
v_trueEqFalse_4149_ = v___x_3922_;
v___y_4150_ = v___y_4197_;
v___y_4151_ = v___y_4196_;
v___y_4152_ = v___y_4204_;
v___y_4153_ = v___y_4201_;
v___y_4154_ = v___y_4192_;
v___y_4155_ = v___y_4193_;
v___y_4156_ = v___y_4203_;
v___y_4157_ = v___y_4198_;
v___y_4158_ = v___y_4194_;
v___y_4159_ = v___y_4195_;
goto v___jp_4144_;
}
else
{
v___y_4145_ = v___y_4202_;
v_interpreted_4146_ = v_interpreted_4206_;
v___y_4147_ = v___y_4200_;
v_valueInconsistency_4148_ = v___x_3926_;
v_trueEqFalse_4149_ = v___x_3922_;
v___y_4150_ = v___y_4197_;
v___y_4151_ = v___y_4196_;
v___y_4152_ = v___y_4204_;
v___y_4153_ = v___y_4201_;
v___y_4154_ = v___y_4192_;
v___y_4155_ = v___y_4193_;
v___y_4156_ = v___y_4203_;
v___y_4157_ = v___y_4198_;
v___y_4158_ = v___y_4194_;
v___y_4159_ = v___y_4195_;
goto v___jp_4144_;
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
lean_dec_ref(v___y_4202_);
lean_dec_ref(v___y_4200_);
lean_dec(v_a_3919_);
lean_dec(v_a_3916_);
lean_dec_ref(v_proof_3898_);
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
v_a_4211_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4208_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4208_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
else
{
v___y_4162_ = v___y_4202_;
v___y_4163_ = v___y_4200_;
v_valueInconsistency_4164_ = v___x_3926_;
v_trueEqFalse_4165_ = v___x_3922_;
v___y_4166_ = v___y_4197_;
v___y_4167_ = v___y_4196_;
v___y_4168_ = v___y_4204_;
v___y_4169_ = v___y_4201_;
v___y_4170_ = v___y_4192_;
v___y_4171_ = v___y_4193_;
v___y_4172_ = v___y_4203_;
v___y_4173_ = v___y_4198_;
v___y_4174_ = v___y_4194_;
v___y_4175_ = v___y_4195_;
goto v___jp_4161_;
}
}
v___jp_4219_:
{
if (v___y_4232_ == 0)
{
v___y_4162_ = v___y_4231_;
v___y_4163_ = v___y_4228_;
v_valueInconsistency_4164_ = v___x_3922_;
v_trueEqFalse_4165_ = v___x_3922_;
v___y_4166_ = v___y_4225_;
v___y_4167_ = v___y_4223_;
v___y_4168_ = v___y_4229_;
v___y_4169_ = v___y_4227_;
v___y_4170_ = v___y_4220_;
v___y_4171_ = v___y_4221_;
v___y_4172_ = v___y_4230_;
v___y_4173_ = v___y_4226_;
v___y_4174_ = v___y_4222_;
v___y_4175_ = v___y_4224_;
goto v___jp_4161_;
}
else
{
uint8_t v___x_4233_; 
lean_inc_ref(v_root_3920_);
v___x_4233_ = l_Lean_Expr_isTrue(v_root_3920_);
if (v___x_4233_ == 0)
{
uint8_t v___x_4234_; 
lean_inc_ref(v_root_3921_);
v___x_4234_ = l_Lean_Expr_isTrue(v_root_3921_);
if (v___x_4234_ == 0)
{
if (v_isHEq_3899_ == 0)
{
uint8_t v_heqProofs_4235_; 
v_heqProofs_4235_ = lean_ctor_get_uint8(v___y_4231_, sizeof(void*)*11 + 4);
if (v_heqProofs_4235_ == 0)
{
uint8_t v_heqProofs_4236_; 
v_heqProofs_4236_ = lean_ctor_get_uint8(v___y_4228_, sizeof(void*)*11 + 4);
if (v_heqProofs_4236_ == 0)
{
uint8_t v_interpreted_4237_; 
v_interpreted_4237_ = lean_ctor_get_uint8(v___y_4231_, sizeof(void*)*11 + 1);
v___y_4145_ = v___y_4231_;
v_interpreted_4146_ = v_interpreted_4237_;
v___y_4147_ = v___y_4228_;
v_valueInconsistency_4148_ = v___x_3926_;
v_trueEqFalse_4149_ = v___x_3922_;
v___y_4150_ = v___y_4225_;
v___y_4151_ = v___y_4223_;
v___y_4152_ = v___y_4229_;
v___y_4153_ = v___y_4227_;
v___y_4154_ = v___y_4220_;
v___y_4155_ = v___y_4221_;
v___y_4156_ = v___y_4230_;
v___y_4157_ = v___y_4226_;
v___y_4158_ = v___y_4222_;
v___y_4159_ = v___y_4224_;
goto v___jp_4144_;
}
else
{
v___y_4192_ = v___y_4220_;
v___y_4193_ = v___y_4221_;
v___y_4194_ = v___y_4222_;
v___y_4195_ = v___y_4224_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___y_4225_;
v___y_4198_ = v___y_4226_;
v___y_4199_ = v___x_4234_;
v___y_4200_ = v___y_4228_;
v___y_4201_ = v___y_4227_;
v___y_4202_ = v___y_4231_;
v___y_4203_ = v___y_4230_;
v___y_4204_ = v___y_4229_;
goto v___jp_4191_;
}
}
else
{
v___y_4192_ = v___y_4220_;
v___y_4193_ = v___y_4221_;
v___y_4194_ = v___y_4222_;
v___y_4195_ = v___y_4224_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___y_4225_;
v___y_4198_ = v___y_4226_;
v___y_4199_ = v___x_4234_;
v___y_4200_ = v___y_4228_;
v___y_4201_ = v___y_4227_;
v___y_4202_ = v___y_4231_;
v___y_4203_ = v___y_4230_;
v___y_4204_ = v___y_4229_;
goto v___jp_4191_;
}
}
else
{
v___y_4192_ = v___y_4220_;
v___y_4193_ = v___y_4221_;
v___y_4194_ = v___y_4222_;
v___y_4195_ = v___y_4224_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___y_4225_;
v___y_4198_ = v___y_4226_;
v___y_4199_ = v___x_4234_;
v___y_4200_ = v___y_4228_;
v___y_4201_ = v___y_4227_;
v___y_4202_ = v___y_4231_;
v___y_4203_ = v___y_4230_;
v___y_4204_ = v___y_4229_;
goto v___jp_4191_;
}
}
else
{
v___y_4178_ = v___y_4220_;
v___y_4179_ = v___y_4221_;
v___y_4180_ = v___y_4222_;
v___y_4181_ = v___y_4224_;
v___y_4182_ = v___y_4223_;
v___y_4183_ = v___y_4225_;
v___y_4184_ = v___y_4226_;
v___y_4185_ = v___y_4227_;
v___y_4186_ = v___y_4228_;
v___y_4187_ = v___y_4230_;
v___y_4188_ = v___y_4229_;
v___y_4189_ = v___y_4231_;
goto v___jp_4177_;
}
}
else
{
v___y_4178_ = v___y_4220_;
v___y_4179_ = v___y_4221_;
v___y_4180_ = v___y_4222_;
v___y_4181_ = v___y_4224_;
v___y_4182_ = v___y_4223_;
v___y_4183_ = v___y_4225_;
v___y_4184_ = v___y_4226_;
v___y_4185_ = v___y_4227_;
v___y_4186_ = v___y_4228_;
v___y_4187_ = v___y_4230_;
v___y_4188_ = v___y_4229_;
v___y_4189_ = v___y_4231_;
goto v___jp_4177_;
}
}
}
v___jp_4238_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = lean_st_ref_get(v___y_4239_);
lean_inc_ref(v_root_3920_);
v___x_4250_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4249_, v_root_3920_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_a_4251_);
lean_dec_ref(v___x_4250_);
v___x_4252_ = lean_st_ref_get(v___y_4239_);
lean_inc_ref(v_root_3921_);
v___x_4253_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4252_, v_root_3921_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
if (lean_obj_tag(v___x_4253_) == 0)
{
uint8_t v_interpreted_4254_; 
v_interpreted_4254_ = lean_ctor_get_uint8(v_a_4251_, sizeof(void*)*11 + 1);
if (v_interpreted_4254_ == 0)
{
lean_object* v_a_4255_; 
v_a_4255_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4255_);
lean_dec_ref(v___x_4253_);
v___y_4220_ = v___y_4243_;
v___y_4221_ = v___y_4244_;
v___y_4222_ = v___y_4247_;
v___y_4223_ = v___y_4240_;
v___y_4224_ = v___y_4248_;
v___y_4225_ = v___y_4239_;
v___y_4226_ = v___y_4246_;
v___y_4227_ = v___y_4242_;
v___y_4228_ = v_a_4255_;
v___y_4229_ = v___y_4241_;
v___y_4230_ = v___y_4245_;
v___y_4231_ = v_a_4251_;
v___y_4232_ = v___x_3922_;
goto v___jp_4219_;
}
else
{
lean_object* v_a_4256_; uint8_t v_interpreted_4257_; 
v_a_4256_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4256_);
lean_dec_ref(v___x_4253_);
v_interpreted_4257_ = lean_ctor_get_uint8(v_a_4256_, sizeof(void*)*11 + 1);
v___y_4220_ = v___y_4243_;
v___y_4221_ = v___y_4244_;
v___y_4222_ = v___y_4247_;
v___y_4223_ = v___y_4240_;
v___y_4224_ = v___y_4248_;
v___y_4225_ = v___y_4239_;
v___y_4226_ = v___y_4246_;
v___y_4227_ = v___y_4242_;
v___y_4228_ = v_a_4256_;
v___y_4229_ = v___y_4241_;
v___y_4230_ = v___y_4245_;
v___y_4231_ = v_a_4251_;
v___y_4232_ = v_interpreted_4257_;
goto v___jp_4219_;
}
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
lean_dec(v_a_4251_);
lean_dec(v_a_3919_);
lean_dec(v_a_3916_);
lean_dec_ref(v_proof_3898_);
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
v_a_4258_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4253_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4253_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
lean_dec(v_a_3919_);
lean_dec(v_a_3916_);
lean_dec_ref(v_proof_3898_);
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
v_a_4266_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___x_4250_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4250_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
}
else
{
lean_object* v_options_4293_; uint8_t v_hasTrace_4294_; 
lean_dec(v_a_3919_);
lean_dec(v_a_3916_);
lean_dec_ref(v_proof_3898_);
v_options_4293_ = lean_ctor_get(v_a_3908_, 2);
v_hasTrace_4294_ = lean_ctor_get_uint8(v_options_4293_, sizeof(void*)*1);
if (v_hasTrace_4294_ == 0)
{
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
goto v___jp_3911_;
}
else
{
lean_object* v_inheritedTraceOptions_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; 
v_inheritedTraceOptions_4295_ = lean_ctor_get(v_a_3908_, 13);
v___x_4296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4298_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4295_, v_options_4293_, v___x_4297_);
if (v___x_4298_ == 0)
{
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
goto v___jp_3911_;
}
else
{
lean_object* v___x_4299_; 
v___x_4299_ = l_Lean_Meta_Grind_updateLastTag(v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v___x_4300_; 
lean_dec_ref(v___x_4299_);
v___x_4300_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3896_, v_a_3900_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4302_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref(v___x_4300_);
v___x_4302_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3897_, v_a_3900_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref(v___x_4302_);
v___x_4304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4305_, 0, v_a_4301_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
lean_ctor_set(v___x_4306_, 1, v_a_4303_);
v___x_4307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4306_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
v___x_4309_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4296_, v___x_4308_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_dec_ref(v___x_4309_);
goto v___jp_3911_;
}
else
{
return v___x_4309_;
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_dec(v_a_4301_);
v_a_4310_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4302_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4302_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec_ref(v_rhs_3897_);
v_a_4318_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4300_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4300_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
return v___x_4299_;
}
}
}
}
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_dec(v_a_3916_);
lean_dec_ref(v_proof_3898_);
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
v_a_4326_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_3918_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_3918_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec_ref(v_proof_3898_);
lean_dec_ref(v_rhs_3897_);
lean_dec_ref(v_lhs_3896_);
v_a_4334_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_3915_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_3915_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
v___jp_3911_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = lean_box(0);
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
return v___x_3913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4342_, lean_object* v_rhs_4343_, lean_object* v_proof_4344_, lean_object* v_isHEq_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_){
_start:
{
uint8_t v_isHEq_boxed_4357_; lean_object* v_res_4358_; 
v_isHEq_boxed_4357_ = lean_unbox(v_isHEq_4345_);
v_res_4358_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4342_, v_rhs_4343_, v_proof_4344_, v_isHEq_boxed_4357_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec(v_a_4353_);
lean_dec_ref(v_a_4352_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
lean_dec(v_a_4346_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4361_){
_start:
{
lean_object* v___x_4363_; lean_object* v_toGoalState_4364_; lean_object* v_mvarId_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4401_; 
v___x_4363_ = lean_st_ref_take(v_a_4361_);
v_toGoalState_4364_ = lean_ctor_get(v___x_4363_, 0);
v_mvarId_4365_ = lean_ctor_get(v___x_4363_, 1);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4367_ = v___x_4363_;
v_isShared_4368_ = v_isSharedCheck_4401_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_mvarId_4365_);
lean_inc(v_toGoalState_4364_);
lean_dec(v___x_4363_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4401_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v_nextDeclIdx_4369_; lean_object* v_enodeMap_4370_; lean_object* v_exprs_4371_; lean_object* v_parents_4372_; lean_object* v_congrTable_4373_; lean_object* v_appMap_4374_; lean_object* v_indicesFound_4375_; uint8_t v_inconsistent_4376_; lean_object* v_nextIdx_4377_; lean_object* v_newRawFacts_4378_; lean_object* v_facts_4379_; lean_object* v_extThms_4380_; lean_object* v_ematch_4381_; lean_object* v_inj_4382_; lean_object* v_split_4383_; lean_object* v_clean_4384_; lean_object* v_sstates_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4399_; 
v_nextDeclIdx_4369_ = lean_ctor_get(v_toGoalState_4364_, 0);
v_enodeMap_4370_ = lean_ctor_get(v_toGoalState_4364_, 1);
v_exprs_4371_ = lean_ctor_get(v_toGoalState_4364_, 2);
v_parents_4372_ = lean_ctor_get(v_toGoalState_4364_, 3);
v_congrTable_4373_ = lean_ctor_get(v_toGoalState_4364_, 4);
v_appMap_4374_ = lean_ctor_get(v_toGoalState_4364_, 5);
v_indicesFound_4375_ = lean_ctor_get(v_toGoalState_4364_, 6);
v_inconsistent_4376_ = lean_ctor_get_uint8(v_toGoalState_4364_, sizeof(void*)*17);
v_nextIdx_4377_ = lean_ctor_get(v_toGoalState_4364_, 8);
v_newRawFacts_4378_ = lean_ctor_get(v_toGoalState_4364_, 9);
v_facts_4379_ = lean_ctor_get(v_toGoalState_4364_, 10);
v_extThms_4380_ = lean_ctor_get(v_toGoalState_4364_, 11);
v_ematch_4381_ = lean_ctor_get(v_toGoalState_4364_, 12);
v_inj_4382_ = lean_ctor_get(v_toGoalState_4364_, 13);
v_split_4383_ = lean_ctor_get(v_toGoalState_4364_, 14);
v_clean_4384_ = lean_ctor_get(v_toGoalState_4364_, 15);
v_sstates_4385_ = lean_ctor_get(v_toGoalState_4364_, 16);
v_isSharedCheck_4399_ = !lean_is_exclusive(v_toGoalState_4364_);
if (v_isSharedCheck_4399_ == 0)
{
lean_object* v_unused_4400_; 
v_unused_4400_ = lean_ctor_get(v_toGoalState_4364_, 7);
lean_dec(v_unused_4400_);
v___x_4387_ = v_toGoalState_4364_;
v_isShared_4388_ = v_isSharedCheck_4399_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_sstates_4385_);
lean_inc(v_clean_4384_);
lean_inc(v_split_4383_);
lean_inc(v_inj_4382_);
lean_inc(v_ematch_4381_);
lean_inc(v_extThms_4380_);
lean_inc(v_facts_4379_);
lean_inc(v_newRawFacts_4378_);
lean_inc(v_nextIdx_4377_);
lean_inc(v_indicesFound_4375_);
lean_inc(v_appMap_4374_);
lean_inc(v_congrTable_4373_);
lean_inc(v_parents_4372_);
lean_inc(v_exprs_4371_);
lean_inc(v_enodeMap_4370_);
lean_inc(v_nextDeclIdx_4369_);
lean_dec(v_toGoalState_4364_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4399_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4389_; lean_object* v___x_4391_; 
v___x_4389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 7, v___x_4389_);
v___x_4391_ = v___x_4387_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_nextDeclIdx_4369_);
lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_enodeMap_4370_);
lean_ctor_set(v_reuseFailAlloc_4398_, 2, v_exprs_4371_);
lean_ctor_set(v_reuseFailAlloc_4398_, 3, v_parents_4372_);
lean_ctor_set(v_reuseFailAlloc_4398_, 4, v_congrTable_4373_);
lean_ctor_set(v_reuseFailAlloc_4398_, 5, v_appMap_4374_);
lean_ctor_set(v_reuseFailAlloc_4398_, 6, v_indicesFound_4375_);
lean_ctor_set(v_reuseFailAlloc_4398_, 7, v___x_4389_);
lean_ctor_set(v_reuseFailAlloc_4398_, 8, v_nextIdx_4377_);
lean_ctor_set(v_reuseFailAlloc_4398_, 9, v_newRawFacts_4378_);
lean_ctor_set(v_reuseFailAlloc_4398_, 10, v_facts_4379_);
lean_ctor_set(v_reuseFailAlloc_4398_, 11, v_extThms_4380_);
lean_ctor_set(v_reuseFailAlloc_4398_, 12, v_ematch_4381_);
lean_ctor_set(v_reuseFailAlloc_4398_, 13, v_inj_4382_);
lean_ctor_set(v_reuseFailAlloc_4398_, 14, v_split_4383_);
lean_ctor_set(v_reuseFailAlloc_4398_, 15, v_clean_4384_);
lean_ctor_set(v_reuseFailAlloc_4398_, 16, v_sstates_4385_);
lean_ctor_set_uint8(v_reuseFailAlloc_4398_, sizeof(void*)*17, v_inconsistent_4376_);
v___x_4391_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
lean_object* v___x_4393_; 
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 0, v___x_4391_);
v___x_4393_ = v___x_4367_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4391_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v_mvarId_4365_);
v___x_4393_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4394_ = lean_st_ref_set(v_a_4361_, v___x_4393_);
v___x_4395_ = lean_box(0);
v___x_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
return v___x_4396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4402_, lean_object* v_a_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4402_);
lean_dec(v_a_4402_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v___x_4416_; 
v___x_4416_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4405_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
lean_dec(v_a_4426_);
lean_dec_ref(v_a_4425_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
lean_dec(v_a_4422_);
lean_dec_ref(v_a_4421_);
lean_dec(v_a_4420_);
lean_dec_ref(v_a_4419_);
lean_dec(v_a_4418_);
lean_dec(v_a_4417_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4429_){
_start:
{
lean_object* v___x_4431_; lean_object* v_toGoalState_4432_; lean_object* v_newFacts_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; uint8_t v___x_4437_; 
v___x_4431_ = lean_st_ref_get(v_a_4429_);
v_toGoalState_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc_ref(v_toGoalState_4432_);
lean_dec(v___x_4431_);
v_newFacts_4433_ = lean_ctor_get(v_toGoalState_4432_, 7);
lean_inc_ref(v_newFacts_4433_);
lean_dec_ref(v_toGoalState_4432_);
v___x_4434_ = lean_array_get_size(v_newFacts_4433_);
v___x_4435_ = lean_unsigned_to_nat(1u);
v___x_4436_ = lean_nat_sub(v___x_4434_, v___x_4435_);
v___x_4437_ = lean_nat_dec_lt(v___x_4436_, v___x_4434_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
lean_dec(v___x_4436_);
lean_dec_ref(v_newFacts_4433_);
v___x_4438_ = lean_box(0);
v___x_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4438_);
return v___x_4439_;
}
else
{
lean_object* v___x_4440_; lean_object* v_toGoalState_4441_; lean_object* v_mvarId_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4479_; 
v___x_4440_ = lean_st_ref_take(v_a_4429_);
v_toGoalState_4441_ = lean_ctor_get(v___x_4440_, 0);
v_mvarId_4442_ = lean_ctor_get(v___x_4440_, 1);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4444_ = v___x_4440_;
v_isShared_4445_ = v_isSharedCheck_4479_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_mvarId_4442_);
lean_inc(v_toGoalState_4441_);
lean_dec(v___x_4440_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4479_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v_nextDeclIdx_4446_; lean_object* v_enodeMap_4447_; lean_object* v_exprs_4448_; lean_object* v_parents_4449_; lean_object* v_congrTable_4450_; lean_object* v_appMap_4451_; lean_object* v_indicesFound_4452_; lean_object* v_newFacts_4453_; uint8_t v_inconsistent_4454_; lean_object* v_nextIdx_4455_; lean_object* v_newRawFacts_4456_; lean_object* v_facts_4457_; lean_object* v_extThms_4458_; lean_object* v_ematch_4459_; lean_object* v_inj_4460_; lean_object* v_split_4461_; lean_object* v_clean_4462_; lean_object* v_sstates_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4478_; 
v_nextDeclIdx_4446_ = lean_ctor_get(v_toGoalState_4441_, 0);
v_enodeMap_4447_ = lean_ctor_get(v_toGoalState_4441_, 1);
v_exprs_4448_ = lean_ctor_get(v_toGoalState_4441_, 2);
v_parents_4449_ = lean_ctor_get(v_toGoalState_4441_, 3);
v_congrTable_4450_ = lean_ctor_get(v_toGoalState_4441_, 4);
v_appMap_4451_ = lean_ctor_get(v_toGoalState_4441_, 5);
v_indicesFound_4452_ = lean_ctor_get(v_toGoalState_4441_, 6);
v_newFacts_4453_ = lean_ctor_get(v_toGoalState_4441_, 7);
v_inconsistent_4454_ = lean_ctor_get_uint8(v_toGoalState_4441_, sizeof(void*)*17);
v_nextIdx_4455_ = lean_ctor_get(v_toGoalState_4441_, 8);
v_newRawFacts_4456_ = lean_ctor_get(v_toGoalState_4441_, 9);
v_facts_4457_ = lean_ctor_get(v_toGoalState_4441_, 10);
v_extThms_4458_ = lean_ctor_get(v_toGoalState_4441_, 11);
v_ematch_4459_ = lean_ctor_get(v_toGoalState_4441_, 12);
v_inj_4460_ = lean_ctor_get(v_toGoalState_4441_, 13);
v_split_4461_ = lean_ctor_get(v_toGoalState_4441_, 14);
v_clean_4462_ = lean_ctor_get(v_toGoalState_4441_, 15);
v_sstates_4463_ = lean_ctor_get(v_toGoalState_4441_, 16);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_toGoalState_4441_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4465_ = v_toGoalState_4441_;
v_isShared_4466_ = v_isSharedCheck_4478_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_sstates_4463_);
lean_inc(v_clean_4462_);
lean_inc(v_split_4461_);
lean_inc(v_inj_4460_);
lean_inc(v_ematch_4459_);
lean_inc(v_extThms_4458_);
lean_inc(v_facts_4457_);
lean_inc(v_newRawFacts_4456_);
lean_inc(v_nextIdx_4455_);
lean_inc(v_newFacts_4453_);
lean_inc(v_indicesFound_4452_);
lean_inc(v_appMap_4451_);
lean_inc(v_congrTable_4450_);
lean_inc(v_parents_4449_);
lean_inc(v_exprs_4448_);
lean_inc(v_enodeMap_4447_);
lean_inc(v_nextDeclIdx_4446_);
lean_dec(v_toGoalState_4441_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4478_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4467_ = lean_array_pop(v_newFacts_4453_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 7, v___x_4467_);
v___x_4469_ = v___x_4465_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_nextDeclIdx_4446_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_enodeMap_4447_);
lean_ctor_set(v_reuseFailAlloc_4477_, 2, v_exprs_4448_);
lean_ctor_set(v_reuseFailAlloc_4477_, 3, v_parents_4449_);
lean_ctor_set(v_reuseFailAlloc_4477_, 4, v_congrTable_4450_);
lean_ctor_set(v_reuseFailAlloc_4477_, 5, v_appMap_4451_);
lean_ctor_set(v_reuseFailAlloc_4477_, 6, v_indicesFound_4452_);
lean_ctor_set(v_reuseFailAlloc_4477_, 7, v___x_4467_);
lean_ctor_set(v_reuseFailAlloc_4477_, 8, v_nextIdx_4455_);
lean_ctor_set(v_reuseFailAlloc_4477_, 9, v_newRawFacts_4456_);
lean_ctor_set(v_reuseFailAlloc_4477_, 10, v_facts_4457_);
lean_ctor_set(v_reuseFailAlloc_4477_, 11, v_extThms_4458_);
lean_ctor_set(v_reuseFailAlloc_4477_, 12, v_ematch_4459_);
lean_ctor_set(v_reuseFailAlloc_4477_, 13, v_inj_4460_);
lean_ctor_set(v_reuseFailAlloc_4477_, 14, v_split_4461_);
lean_ctor_set(v_reuseFailAlloc_4477_, 15, v_clean_4462_);
lean_ctor_set(v_reuseFailAlloc_4477_, 16, v_sstates_4463_);
lean_ctor_set_uint8(v_reuseFailAlloc_4477_, sizeof(void*)*17, v_inconsistent_4454_);
v___x_4469_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
lean_object* v___x_4471_; 
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 0, v___x_4469_);
v___x_4471_ = v___x_4444_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4469_);
lean_ctor_set(v_reuseFailAlloc_4476_, 1, v_mvarId_4442_);
v___x_4471_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4472_ = lean_st_ref_set(v_a_4429_, v___x_4471_);
v___x_4473_ = lean_array_fget(v_newFacts_4433_, v___x_4436_);
lean_dec(v___x_4436_);
lean_dec_ref(v_newFacts_4433_);
v___x_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4474_, 0, v___x_4473_);
v___x_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4474_);
return v___x_4475_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4480_);
lean_dec(v_a_4480_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4483_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec_ref(v_a_4499_);
lean_dec(v_a_4498_);
lean_dec_ref(v_a_4497_);
lean_dec(v_a_4496_);
lean_dec(v_a_4495_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4507_, lean_object* v_rhs_4508_, lean_object* v_proof_4509_, uint8_t v_isHEq_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_){
_start:
{
lean_object* v___x_4522_; 
v___x_4522_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4507_, v_rhs_4508_, v_proof_4509_, v_isHEq_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v___x_4523_; 
lean_dec_ref(v___x_4522_);
lean_inc(v_a_4520_);
lean_inc_ref(v_a_4519_);
lean_inc(v_a_4518_);
lean_inc_ref(v_a_4517_);
lean_inc(v_a_4516_);
lean_inc_ref(v_a_4515_);
lean_inc(v_a_4514_);
lean_inc_ref(v_a_4513_);
lean_inc(v_a_4512_);
lean_inc(v_a_4511_);
v___x_4523_ = lean_grind_process_new_facts(v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
return v___x_4523_;
}
else
{
return v___x_4522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4524_, lean_object* v_rhs_4525_, lean_object* v_proof_4526_, lean_object* v_isHEq_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_){
_start:
{
uint8_t v_isHEq_boxed_4539_; lean_object* v_res_4540_; 
v_isHEq_boxed_4539_ = lean_unbox(v_isHEq_4527_);
v_res_4540_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4524_, v_rhs_4525_, v_proof_4526_, v_isHEq_boxed_4539_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_);
lean_dec(v_a_4537_);
lean_dec_ref(v_a_4536_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec(v_a_4529_);
lean_dec(v_a_4528_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4541_, lean_object* v_rhs_4542_, lean_object* v_proof_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
uint8_t v___x_4555_; lean_object* v___x_4556_; 
v___x_4555_ = 0;
v___x_4556_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4541_, v_rhs_4542_, v_proof_4543_, v___x_4555_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4557_, lean_object* v_rhs_4558_, lean_object* v_proof_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4557_, v_rhs_4558_, v_proof_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec(v_a_4560_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4572_, lean_object* v_rhs_4573_, lean_object* v_proof_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_){
_start:
{
uint8_t v___x_4586_; lean_object* v___x_4587_; 
v___x_4586_ = 1;
v___x_4587_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4572_, v_rhs_4573_, v_proof_4574_, v___x_4586_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
return v___x_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4588_, lean_object* v_rhs_4589_, lean_object* v_proof_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4588_, v_rhs_4589_, v_proof_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
lean_dec(v_a_4598_);
lean_dec_ref(v_a_4597_);
lean_dec(v_a_4596_);
lean_dec_ref(v_a_4595_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
lean_dec(v_a_4592_);
lean_dec(v_a_4591_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v___x_4606_; lean_object* v_toGoalState_4607_; lean_object* v_mvarId_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4644_; 
v___x_4606_ = lean_st_ref_take(v_a_4604_);
v_toGoalState_4607_ = lean_ctor_get(v___x_4606_, 0);
v_mvarId_4608_ = lean_ctor_get(v___x_4606_, 1);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4610_ = v___x_4606_;
v_isShared_4611_ = v_isSharedCheck_4644_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_mvarId_4608_);
lean_inc(v_toGoalState_4607_);
lean_dec(v___x_4606_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4644_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v_nextDeclIdx_4612_; lean_object* v_enodeMap_4613_; lean_object* v_exprs_4614_; lean_object* v_parents_4615_; lean_object* v_congrTable_4616_; lean_object* v_appMap_4617_; lean_object* v_indicesFound_4618_; lean_object* v_newFacts_4619_; uint8_t v_inconsistent_4620_; lean_object* v_nextIdx_4621_; lean_object* v_newRawFacts_4622_; lean_object* v_facts_4623_; lean_object* v_extThms_4624_; lean_object* v_ematch_4625_; lean_object* v_inj_4626_; lean_object* v_split_4627_; lean_object* v_clean_4628_; lean_object* v_sstates_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4643_; 
v_nextDeclIdx_4612_ = lean_ctor_get(v_toGoalState_4607_, 0);
v_enodeMap_4613_ = lean_ctor_get(v_toGoalState_4607_, 1);
v_exprs_4614_ = lean_ctor_get(v_toGoalState_4607_, 2);
v_parents_4615_ = lean_ctor_get(v_toGoalState_4607_, 3);
v_congrTable_4616_ = lean_ctor_get(v_toGoalState_4607_, 4);
v_appMap_4617_ = lean_ctor_get(v_toGoalState_4607_, 5);
v_indicesFound_4618_ = lean_ctor_get(v_toGoalState_4607_, 6);
v_newFacts_4619_ = lean_ctor_get(v_toGoalState_4607_, 7);
v_inconsistent_4620_ = lean_ctor_get_uint8(v_toGoalState_4607_, sizeof(void*)*17);
v_nextIdx_4621_ = lean_ctor_get(v_toGoalState_4607_, 8);
v_newRawFacts_4622_ = lean_ctor_get(v_toGoalState_4607_, 9);
v_facts_4623_ = lean_ctor_get(v_toGoalState_4607_, 10);
v_extThms_4624_ = lean_ctor_get(v_toGoalState_4607_, 11);
v_ematch_4625_ = lean_ctor_get(v_toGoalState_4607_, 12);
v_inj_4626_ = lean_ctor_get(v_toGoalState_4607_, 13);
v_split_4627_ = lean_ctor_get(v_toGoalState_4607_, 14);
v_clean_4628_ = lean_ctor_get(v_toGoalState_4607_, 15);
v_sstates_4629_ = lean_ctor_get(v_toGoalState_4607_, 16);
v_isSharedCheck_4643_ = !lean_is_exclusive(v_toGoalState_4607_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4631_ = v_toGoalState_4607_;
v_isShared_4632_ = v_isSharedCheck_4643_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_sstates_4629_);
lean_inc(v_clean_4628_);
lean_inc(v_split_4627_);
lean_inc(v_inj_4626_);
lean_inc(v_ematch_4625_);
lean_inc(v_extThms_4624_);
lean_inc(v_facts_4623_);
lean_inc(v_newRawFacts_4622_);
lean_inc(v_nextIdx_4621_);
lean_inc(v_newFacts_4619_);
lean_inc(v_indicesFound_4618_);
lean_inc(v_appMap_4617_);
lean_inc(v_congrTable_4616_);
lean_inc(v_parents_4615_);
lean_inc(v_exprs_4614_);
lean_inc(v_enodeMap_4613_);
lean_inc(v_nextDeclIdx_4612_);
lean_dec(v_toGoalState_4607_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4643_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4633_; lean_object* v___x_4635_; 
v___x_4633_ = l_Lean_PersistentArray_push___redArg(v_facts_4623_, v_fact_4603_);
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 10, v___x_4633_);
v___x_4635_ = v___x_4631_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_nextDeclIdx_4612_);
lean_ctor_set(v_reuseFailAlloc_4642_, 1, v_enodeMap_4613_);
lean_ctor_set(v_reuseFailAlloc_4642_, 2, v_exprs_4614_);
lean_ctor_set(v_reuseFailAlloc_4642_, 3, v_parents_4615_);
lean_ctor_set(v_reuseFailAlloc_4642_, 4, v_congrTable_4616_);
lean_ctor_set(v_reuseFailAlloc_4642_, 5, v_appMap_4617_);
lean_ctor_set(v_reuseFailAlloc_4642_, 6, v_indicesFound_4618_);
lean_ctor_set(v_reuseFailAlloc_4642_, 7, v_newFacts_4619_);
lean_ctor_set(v_reuseFailAlloc_4642_, 8, v_nextIdx_4621_);
lean_ctor_set(v_reuseFailAlloc_4642_, 9, v_newRawFacts_4622_);
lean_ctor_set(v_reuseFailAlloc_4642_, 10, v___x_4633_);
lean_ctor_set(v_reuseFailAlloc_4642_, 11, v_extThms_4624_);
lean_ctor_set(v_reuseFailAlloc_4642_, 12, v_ematch_4625_);
lean_ctor_set(v_reuseFailAlloc_4642_, 13, v_inj_4626_);
lean_ctor_set(v_reuseFailAlloc_4642_, 14, v_split_4627_);
lean_ctor_set(v_reuseFailAlloc_4642_, 15, v_clean_4628_);
lean_ctor_set(v_reuseFailAlloc_4642_, 16, v_sstates_4629_);
lean_ctor_set_uint8(v_reuseFailAlloc_4642_, sizeof(void*)*17, v_inconsistent_4620_);
v___x_4635_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
lean_object* v___x_4637_; 
if (v_isShared_4611_ == 0)
{
lean_ctor_set(v___x_4610_, 0, v___x_4635_);
v___x_4637_ = v___x_4610_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4635_);
lean_ctor_set(v_reuseFailAlloc_4641_, 1, v_mvarId_4608_);
v___x_4637_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4638_ = lean_st_ref_set(v_a_4604_, v___x_4637_);
v___x_4639_ = lean_box(0);
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
return v___x_4640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v_res_4648_; 
v_res_4648_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4645_, v_a_4646_);
lean_dec(v_a_4646_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_){
_start:
{
lean_object* v___x_4661_; 
v___x_4661_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4649_, v_a_4650_);
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
lean_dec(v_a_4668_);
lean_dec_ref(v_a_4667_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
lean_dec(v_a_4664_);
lean_dec(v_a_4663_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4675_, lean_object* v_rhs_4676_, lean_object* v_proof_4677_, lean_object* v_generation_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4690_; 
lean_inc_ref(v_rhs_4676_);
lean_inc_ref(v_lhs_4675_);
v___x_4690_ = l_Lean_Meta_mkEq(v_lhs_4675_, v_rhs_4676_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4702_; 
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
lean_inc_n(v_a_4691_, 2);
lean_dec_ref(v___x_4690_);
v___x_4692_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4691_, v_a_4679_);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4702_ == 0)
{
lean_object* v_unused_4703_; 
v_unused_4703_ = lean_ctor_get(v___x_4692_, 0);
lean_dec(v_unused_4703_);
v___x_4694_ = v___x_4692_;
v_isShared_4695_ = v_isSharedCheck_4702_;
goto v_resetjp_4693_;
}
else
{
lean_dec(v___x_4692_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4702_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
lean_ctor_set_tag(v___x_4694_, 1);
lean_ctor_set(v___x_4694_, 0, v_a_4691_);
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4691_);
v___x_4697_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
lean_object* v___x_4698_; 
lean_inc(v_a_4688_);
lean_inc_ref(v_a_4687_);
lean_inc(v_a_4686_);
lean_inc_ref(v_a_4685_);
lean_inc(v_a_4684_);
lean_inc_ref(v_a_4683_);
lean_inc(v_a_4682_);
lean_inc_ref(v_a_4681_);
lean_inc(v_a_4680_);
lean_inc(v_a_4679_);
lean_inc_ref(v___x_4697_);
lean_inc(v_generation_4678_);
lean_inc_ref(v_lhs_4675_);
v___x_4698_ = lean_grind_internalize(v_lhs_4675_, v_generation_4678_, v___x_4697_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v___x_4699_; 
lean_dec_ref(v___x_4698_);
lean_inc(v_a_4688_);
lean_inc_ref(v_a_4687_);
lean_inc(v_a_4686_);
lean_inc_ref(v_a_4685_);
lean_inc(v_a_4684_);
lean_inc_ref(v_a_4683_);
lean_inc(v_a_4682_);
lean_inc_ref(v_a_4681_);
lean_inc(v_a_4680_);
lean_inc(v_a_4679_);
lean_inc_ref(v_rhs_4676_);
v___x_4699_ = lean_grind_internalize(v_rhs_4676_, v_generation_4678_, v___x_4697_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v___x_4700_; 
lean_dec_ref(v___x_4699_);
v___x_4700_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4675_, v_rhs_4676_, v_proof_4677_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
return v___x_4700_;
}
else
{
lean_dec_ref(v_proof_4677_);
lean_dec_ref(v_rhs_4676_);
lean_dec_ref(v_lhs_4675_);
return v___x_4699_;
}
}
else
{
lean_dec_ref(v___x_4697_);
lean_dec(v_generation_4678_);
lean_dec_ref(v_proof_4677_);
lean_dec_ref(v_rhs_4676_);
lean_dec_ref(v_lhs_4675_);
return v___x_4698_;
}
}
}
}
else
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
lean_dec(v_generation_4678_);
lean_dec_ref(v_proof_4677_);
lean_dec_ref(v_rhs_4676_);
lean_dec_ref(v_lhs_4675_);
v_a_4704_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4690_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4690_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4712_, lean_object* v_rhs_4713_, lean_object* v_proof_4714_, lean_object* v_generation_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4712_, v_rhs_4713_, v_proof_4714_, v_generation_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4728_, lean_object* v_generation_4729_, lean_object* v_p_4730_, uint8_t v_isNeg_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4743_ = lean_box(0);
lean_inc(v_a_4741_);
lean_inc_ref(v_a_4740_);
lean_inc(v_a_4739_);
lean_inc_ref(v_a_4738_);
lean_inc(v_a_4737_);
lean_inc_ref(v_a_4736_);
lean_inc(v_a_4735_);
lean_inc_ref(v_a_4734_);
lean_inc(v_a_4733_);
lean_inc(v_a_4732_);
lean_inc_ref(v_p_4730_);
v___x_4744_ = lean_grind_internalize(v_p_4730_, v_generation_4729_, v___x_4743_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_dec_ref(v___x_4744_);
if (v_isNeg_4731_ == 0)
{
lean_object* v___x_4745_; 
v___x_4745_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4736_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4747_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
lean_inc(v_a_4746_);
lean_dec_ref(v___x_4745_);
v___x_4747_ = l_Lean_Meta_mkEqTrue(v_proof_4728_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; lean_object* v___x_4749_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref(v___x_4747_);
v___x_4749_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4730_, v_a_4746_, v_a_4748_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
return v___x_4749_;
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
lean_dec(v_a_4746_);
lean_dec_ref(v_p_4730_);
v_a_4750_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4747_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4747_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
lean_dec_ref(v_p_4730_);
lean_dec_ref(v_proof_4728_);
v_a_4758_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4745_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4745_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
else
{
lean_object* v___x_4766_; 
v___x_4766_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4736_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4768_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
lean_inc(v_a_4767_);
lean_dec_ref(v___x_4766_);
v___x_4768_ = l_Lean_Meta_mkEqFalse(v_proof_4728_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v___x_4770_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
lean_inc(v_a_4769_);
lean_dec_ref(v___x_4768_);
v___x_4770_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4730_, v_a_4767_, v_a_4769_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
return v___x_4770_;
}
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
lean_dec(v_a_4767_);
lean_dec_ref(v_p_4730_);
v_a_4771_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4768_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4768_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
else
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4786_; 
lean_dec_ref(v_p_4730_);
lean_dec_ref(v_proof_4728_);
v_a_4779_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4781_ = v___x_4766_;
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4766_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4784_; 
if (v_isShared_4782_ == 0)
{
v___x_4784_ = v___x_4781_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4779_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4730_);
lean_dec_ref(v_proof_4728_);
return v___x_4744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4787_, lean_object* v_generation_4788_, lean_object* v_p_4789_, lean_object* v_isNeg_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
uint8_t v_isNeg_boxed_4802_; lean_object* v_res_4803_; 
v_isNeg_boxed_4802_ = lean_unbox(v_isNeg_4790_);
v_res_4803_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4787_, v_generation_4788_, v_p_4789_, v_isNeg_boxed_4802_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec(v_a_4796_);
lean_dec_ref(v_a_4795_);
lean_dec(v_a_4794_);
lean_dec_ref(v_a_4793_);
lean_dec(v_a_4792_);
lean_dec(v_a_4791_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4804_, lean_object* v_generation_4805_, lean_object* v_p_4806_, lean_object* v_lhs_4807_, lean_object* v_rhs_4808_, uint8_t v_isNeg_4809_, uint8_t v_isHEq_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_){
_start:
{
if (v_isNeg_4809_ == 0)
{
lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4822_, 0, v_p_4806_);
lean_inc(v_a_4820_);
lean_inc_ref(v_a_4819_);
lean_inc(v_a_4818_);
lean_inc_ref(v_a_4817_);
lean_inc(v_a_4816_);
lean_inc_ref(v_a_4815_);
lean_inc(v_a_4814_);
lean_inc_ref(v_a_4813_);
lean_inc(v_a_4812_);
lean_inc(v_a_4811_);
lean_inc_ref(v___x_4822_);
lean_inc(v_generation_4805_);
lean_inc_ref(v_lhs_4807_);
v___x_4823_ = lean_grind_internalize(v_lhs_4807_, v_generation_4805_, v___x_4822_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v___x_4824_; 
lean_dec_ref(v___x_4823_);
lean_inc(v_a_4820_);
lean_inc_ref(v_a_4819_);
lean_inc(v_a_4818_);
lean_inc_ref(v_a_4817_);
lean_inc(v_a_4816_);
lean_inc_ref(v_a_4815_);
lean_inc(v_a_4814_);
lean_inc_ref(v_a_4813_);
lean_inc(v_a_4812_);
lean_inc(v_a_4811_);
lean_inc_ref(v_rhs_4808_);
v___x_4824_ = lean_grind_internalize(v_rhs_4808_, v_generation_4805_, v___x_4822_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v___x_4825_; 
lean_dec_ref(v___x_4824_);
v___x_4825_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4807_, v_rhs_4808_, v_proof_4804_, v_isHEq_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
return v___x_4825_;
}
else
{
lean_dec_ref(v_rhs_4808_);
lean_dec_ref(v_lhs_4807_);
lean_dec_ref(v_proof_4804_);
return v___x_4824_;
}
}
else
{
lean_dec_ref(v___x_4822_);
lean_dec_ref(v_rhs_4808_);
lean_dec_ref(v_lhs_4807_);
lean_dec(v_generation_4805_);
lean_dec_ref(v_proof_4804_);
return v___x_4823_;
}
}
else
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
lean_dec_ref(v_rhs_4808_);
lean_dec_ref(v_lhs_4807_);
v___x_4826_ = lean_box(0);
lean_inc(v_a_4820_);
lean_inc_ref(v_a_4819_);
lean_inc(v_a_4818_);
lean_inc_ref(v_a_4817_);
lean_inc(v_a_4816_);
lean_inc_ref(v_a_4815_);
lean_inc(v_a_4814_);
lean_inc_ref(v_a_4813_);
lean_inc(v_a_4812_);
lean_inc(v_a_4811_);
lean_inc_ref(v_p_4806_);
v___x_4827_ = lean_grind_internalize(v_p_4806_, v_generation_4805_, v___x_4826_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v___x_4828_; 
lean_dec_ref(v___x_4827_);
v___x_4828_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4815_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v___x_4830_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref(v___x_4828_);
v___x_4830_ = l_Lean_Meta_mkEqFalse(v_proof_4804_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4832_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4831_);
lean_dec_ref(v___x_4830_);
v___x_4832_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4806_, v_a_4829_, v_a_4831_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
return v___x_4832_;
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
lean_dec(v_a_4829_);
lean_dec_ref(v_p_4806_);
v_a_4833_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4830_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4830_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
lean_dec_ref(v_p_4806_);
lean_dec_ref(v_proof_4804_);
v_a_4841_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___x_4828_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4828_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
else
{
lean_dec_ref(v_p_4806_);
lean_dec_ref(v_proof_4804_);
return v___x_4827_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4849_ = _args[0];
lean_object* v_generation_4850_ = _args[1];
lean_object* v_p_4851_ = _args[2];
lean_object* v_lhs_4852_ = _args[3];
lean_object* v_rhs_4853_ = _args[4];
lean_object* v_isNeg_4854_ = _args[5];
lean_object* v_isHEq_4855_ = _args[6];
lean_object* v_a_4856_ = _args[7];
lean_object* v_a_4857_ = _args[8];
lean_object* v_a_4858_ = _args[9];
lean_object* v_a_4859_ = _args[10];
lean_object* v_a_4860_ = _args[11];
lean_object* v_a_4861_ = _args[12];
lean_object* v_a_4862_ = _args[13];
lean_object* v_a_4863_ = _args[14];
lean_object* v_a_4864_ = _args[15];
lean_object* v_a_4865_ = _args[16];
lean_object* v_a_4866_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4867_; uint8_t v_isHEq_boxed_4868_; lean_object* v_res_4869_; 
v_isNeg_boxed_4867_ = lean_unbox(v_isNeg_4854_);
v_isHEq_boxed_4868_ = lean_unbox(v_isHEq_4855_);
v_res_4869_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4849_, v_generation_4850_, v_p_4851_, v_lhs_4852_, v_rhs_4853_, v_isNeg_boxed_4867_, v_isHEq_boxed_4868_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
lean_dec(v_a_4865_);
lean_dec_ref(v_a_4864_);
lean_dec(v_a_4863_);
lean_dec_ref(v_a_4862_);
lean_dec(v_a_4861_);
lean_dec_ref(v_a_4860_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
lean_dec(v_a_4857_);
lean_dec(v_a_4856_);
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4873_, lean_object* v_generation_4874_, lean_object* v_p_4875_, uint8_t v_isNeg_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_){
_start:
{
lean_object* v___x_4888_; 
lean_inc_ref(v_p_4875_);
v___x_4888_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4875_, v_a_4884_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4890_; uint8_t v___x_4891_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_a_4889_);
lean_dec_ref(v___x_4888_);
v___x_4890_ = l_Lean_Expr_cleanupAnnotations(v_a_4889_);
v___x_4891_ = l_Lean_Expr_isApp(v___x_4890_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; 
lean_dec_ref(v___x_4890_);
v___x_4892_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4873_, v_generation_4874_, v_p_4875_, v_isNeg_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
return v___x_4892_;
}
else
{
lean_object* v_arg_4893_; lean_object* v___x_4894_; uint8_t v___x_4895_; 
v_arg_4893_ = lean_ctor_get(v___x_4890_, 1);
lean_inc_ref(v_arg_4893_);
v___x_4894_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4890_);
v___x_4895_ = l_Lean_Expr_isApp(v___x_4894_);
if (v___x_4895_ == 0)
{
lean_object* v___x_4896_; 
lean_dec_ref(v___x_4894_);
lean_dec_ref(v_arg_4893_);
v___x_4896_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4873_, v_generation_4874_, v_p_4875_, v_isNeg_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
return v___x_4896_;
}
else
{
lean_object* v_arg_4897_; lean_object* v___x_4898_; uint8_t v___x_4899_; 
v_arg_4897_ = lean_ctor_get(v___x_4894_, 1);
lean_inc_ref(v_arg_4897_);
v___x_4898_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4894_);
v___x_4899_ = l_Lean_Expr_isApp(v___x_4898_);
if (v___x_4899_ == 0)
{
lean_object* v___x_4900_; 
lean_dec_ref(v___x_4898_);
lean_dec_ref(v_arg_4897_);
lean_dec_ref(v_arg_4893_);
v___x_4900_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4873_, v_generation_4874_, v_p_4875_, v_isNeg_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
return v___x_4900_;
}
else
{
lean_object* v_arg_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; uint8_t v___x_4904_; 
v_arg_4901_ = lean_ctor_get(v___x_4898_, 1);
lean_inc_ref(v_arg_4901_);
v___x_4902_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4898_);
v___x_4903_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_4904_ = l_Lean_Expr_isConstOf(v___x_4902_, v___x_4903_);
if (v___x_4904_ == 0)
{
uint8_t v___x_4905_; 
lean_dec_ref(v_arg_4897_);
v___x_4905_ = l_Lean_Expr_isApp(v___x_4902_);
if (v___x_4905_ == 0)
{
lean_object* v___x_4906_; 
lean_dec_ref(v___x_4902_);
lean_dec_ref(v_arg_4901_);
lean_dec_ref(v_arg_4893_);
v___x_4906_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4873_, v_generation_4874_, v_p_4875_, v_isNeg_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
return v___x_4906_;
}
else
{
lean_object* v___x_4907_; lean_object* v___x_4908_; uint8_t v___x_4909_; 
v___x_4907_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4902_);
v___x_4908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_4909_ = l_Lean_Expr_isConstOf(v___x_4907_, v___x_4908_);
lean_dec_ref(v___x_4907_);
if (v___x_4909_ == 0)
{
lean_object* v___x_4910_; 
lean_dec_ref(v_arg_4901_);
lean_dec_ref(v_arg_4893_);
v___x_4910_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4873_, v_generation_4874_, v_p_4875_, v_isNeg_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
return v___x_4910_;
}
else
{
lean_object* v___x_4911_; 
v___x_4911_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4873_, v_generation_4874_, v_p_4875_, v_arg_4901_, v_arg_4893_, v_isNeg_4876_, v___x_4909_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
return v___x_4911_;
}
}
}
else
{
uint8_t v___x_4912_; 
lean_dec_ref(v___x_4902_);
v___x_4912_ = l_Lean_Expr_isProp(v_arg_4901_);
lean_dec_ref(v_arg_4901_);
if (v___x_4912_ == 0)
{
lean_object* v___x_4913_; 
v___x_4913_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4873_, v_generation_4874_, v_p_4875_, v_arg_4897_, v_arg_4893_, v_isNeg_4876_, v___x_4912_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
return v___x_4913_;
}
else
{
lean_object* v___x_4914_; 
lean_dec_ref(v_arg_4897_);
lean_dec_ref(v_arg_4893_);
v___x_4914_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4873_, v_generation_4874_, v_p_4875_, v_isNeg_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
return v___x_4914_;
}
}
}
}
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
lean_dec_ref(v_p_4875_);
lean_dec(v_generation_4874_);
lean_dec_ref(v_proof_4873_);
v_a_4915_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4888_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4888_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_4923_, lean_object* v_generation_4924_, lean_object* v_p_4925_, lean_object* v_isNeg_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_){
_start:
{
uint8_t v_isNeg_boxed_4938_; lean_object* v_res_4939_; 
v_isNeg_boxed_4938_ = lean_unbox(v_isNeg_4926_);
v_res_4939_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4923_, v_generation_4924_, v_p_4925_, v_isNeg_boxed_4938_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_);
lean_dec(v_a_4936_);
lean_dec_ref(v_a_4935_);
lean_dec(v_a_4934_);
lean_dec_ref(v_a_4933_);
lean_dec(v_a_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v_a_4930_);
lean_dec_ref(v_a_4929_);
lean_dec(v_a_4928_);
lean_dec(v_a_4927_);
return v_res_4939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_4948_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4949_ = l_Lean_Name_append(v___x_4948_, v___x_4947_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_4950_, lean_object* v_proof_4951_, lean_object* v_generation_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_){
_start:
{
lean_object* v___y_4965_; lean_object* v___y_4966_; lean_object* v___y_4967_; lean_object* v___y_4968_; lean_object* v___y_4969_; lean_object* v___y_4970_; lean_object* v___y_4971_; lean_object* v___y_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4982_; lean_object* v___y_4983_; lean_object* v___y_4984_; lean_object* v___y_4985_; lean_object* v___y_4986_; lean_object* v___y_4987_; lean_object* v___x_4995_; lean_object* v_options_4996_; uint8_t v_hasTrace_4997_; 
lean_inc_ref(v_fact_4950_);
v___x_4995_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4950_, v_a_4953_);
lean_dec_ref(v___x_4995_);
v_options_4996_ = lean_ctor_get(v_a_4961_, 2);
v_hasTrace_4997_ = lean_ctor_get_uint8(v_options_4996_, sizeof(void*)*1);
if (v_hasTrace_4997_ == 0)
{
v___y_4978_ = v_a_4953_;
v___y_4979_ = v_a_4954_;
v___y_4980_ = v_a_4955_;
v___y_4981_ = v_a_4956_;
v___y_4982_ = v_a_4957_;
v___y_4983_ = v_a_4958_;
v___y_4984_ = v_a_4959_;
v___y_4985_ = v_a_4960_;
v___y_4986_ = v_a_4961_;
v___y_4987_ = v_a_4962_;
goto v___jp_4977_;
}
else
{
lean_object* v_inheritedTraceOptions_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; uint8_t v___x_5001_; 
v_inheritedTraceOptions_4998_ = lean_ctor_get(v_a_4961_, 13);
v___x_4999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5000_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5001_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4998_, v_options_4996_, v___x_5000_);
if (v___x_5001_ == 0)
{
v___y_4978_ = v_a_4953_;
v___y_4979_ = v_a_4954_;
v___y_4980_ = v_a_4955_;
v___y_4981_ = v_a_4956_;
v___y_4982_ = v_a_4957_;
v___y_4983_ = v_a_4958_;
v___y_4984_ = v_a_4959_;
v___y_4985_ = v_a_4960_;
v___y_4986_ = v_a_4961_;
v___y_4987_ = v_a_4962_;
goto v___jp_4977_;
}
else
{
lean_object* v___x_5002_; 
v___x_5002_ = l_Lean_Meta_Grind_updateLastTag(v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v___x_5003_; lean_object* v___x_5004_; 
lean_dec_ref(v___x_5002_);
lean_inc_ref(v_fact_4950_);
v___x_5003_ = l_Lean_MessageData_ofExpr(v_fact_4950_);
v___x_5004_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4999_, v___x_5003_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
if (lean_obj_tag(v___x_5004_) == 0)
{
lean_dec_ref(v___x_5004_);
v___y_4978_ = v_a_4953_;
v___y_4979_ = v_a_4954_;
v___y_4980_ = v_a_4955_;
v___y_4981_ = v_a_4956_;
v___y_4982_ = v_a_4957_;
v___y_4983_ = v_a_4958_;
v___y_4984_ = v_a_4959_;
v___y_4985_ = v_a_4960_;
v___y_4986_ = v_a_4961_;
v___y_4987_ = v_a_4962_;
goto v___jp_4977_;
}
else
{
lean_dec(v_generation_4952_);
lean_dec_ref(v_proof_4951_);
lean_dec_ref(v_fact_4950_);
return v___x_5004_;
}
}
else
{
lean_dec(v_generation_4952_);
lean_dec_ref(v_proof_4951_);
lean_dec_ref(v_fact_4950_);
return v___x_5002_;
}
}
}
v___jp_4964_:
{
uint8_t v___x_4975_; lean_object* v___x_4976_; 
v___x_4975_ = 0;
v___x_4976_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4951_, v_generation_4952_, v_fact_4950_, v___x_4975_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
return v___x_4976_;
}
v___jp_4977_:
{
lean_object* v___x_4988_; uint8_t v___x_4989_; 
lean_inc_ref(v_fact_4950_);
v___x_4988_ = l_Lean_Expr_cleanupAnnotations(v_fact_4950_);
v___x_4989_ = l_Lean_Expr_isApp(v___x_4988_);
if (v___x_4989_ == 0)
{
lean_dec_ref(v___x_4988_);
v___y_4965_ = v___y_4978_;
v___y_4966_ = v___y_4979_;
v___y_4967_ = v___y_4980_;
v___y_4968_ = v___y_4981_;
v___y_4969_ = v___y_4982_;
v___y_4970_ = v___y_4983_;
v___y_4971_ = v___y_4984_;
v___y_4972_ = v___y_4985_;
v___y_4973_ = v___y_4986_;
v___y_4974_ = v___y_4987_;
goto v___jp_4964_;
}
else
{
lean_object* v_arg_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; uint8_t v___x_4993_; 
v_arg_4990_ = lean_ctor_get(v___x_4988_, 1);
lean_inc_ref(v_arg_4990_);
v___x_4991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4988_);
v___x_4992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_4993_ = l_Lean_Expr_isConstOf(v___x_4991_, v___x_4992_);
lean_dec_ref(v___x_4991_);
if (v___x_4993_ == 0)
{
lean_dec_ref(v_arg_4990_);
v___y_4965_ = v___y_4978_;
v___y_4966_ = v___y_4979_;
v___y_4967_ = v___y_4980_;
v___y_4968_ = v___y_4981_;
v___y_4969_ = v___y_4982_;
v___y_4970_ = v___y_4983_;
v___y_4971_ = v___y_4984_;
v___y_4972_ = v___y_4985_;
v___y_4973_ = v___y_4986_;
v___y_4974_ = v___y_4987_;
goto v___jp_4964_;
}
else
{
lean_object* v___x_4994_; 
lean_dec_ref(v_fact_4950_);
v___x_4994_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_4951_, v_generation_4952_, v_arg_4990_, v___x_4993_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
return v___x_4994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5005_, lean_object* v_proof_5006_, lean_object* v_generation_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5005_, v_proof_5006_, v_generation_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_);
lean_dec(v_a_5017_);
lean_dec_ref(v_a_5016_);
lean_dec(v_a_5015_);
lean_dec_ref(v_a_5014_);
lean_dec(v_a_5013_);
lean_dec_ref(v_a_5012_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec(v_a_5008_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_){
_start:
{
lean_object* v___x_5034_; 
v___x_5034_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5023_);
if (lean_obj_tag(v___x_5034_) == 0)
{
lean_object* v_a_5035_; uint8_t v___x_5036_; 
v_a_5035_ = lean_ctor_get(v___x_5034_, 0);
lean_inc(v_a_5035_);
lean_dec_ref(v___x_5034_);
v___x_5036_ = lean_unbox(v_a_5035_);
lean_dec(v_a_5035_);
if (v___x_5036_ == 0)
{
lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5037_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5038_ = l_Lean_Core_checkSystem(v___x_5037_, v___y_5031_, v___y_5032_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v___x_5039_; 
lean_dec_ref(v___x_5038_);
v___x_5039_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5023_);
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5076_; 
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5042_ = v___x_5039_;
v_isShared_5043_ = v_isSharedCheck_5076_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_5039_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5076_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
if (lean_obj_tag(v_a_5040_) == 1)
{
lean_object* v_val_5044_; 
lean_del_object(v___x_5042_);
v_val_5044_ = lean_ctor_get(v_a_5040_, 0);
lean_inc(v_val_5044_);
lean_dec_ref(v_a_5040_);
if (lean_obj_tag(v_val_5044_) == 0)
{
lean_object* v_lhs_5045_; lean_object* v_rhs_5046_; lean_object* v_proof_5047_; uint8_t v_isHEq_5048_; lean_object* v___x_5049_; 
v_lhs_5045_ = lean_ctor_get(v_val_5044_, 0);
lean_inc_ref(v_lhs_5045_);
v_rhs_5046_ = lean_ctor_get(v_val_5044_, 1);
lean_inc_ref(v_rhs_5046_);
v_proof_5047_ = lean_ctor_get(v_val_5044_, 2);
lean_inc_ref(v_proof_5047_);
v_isHEq_5048_ = lean_ctor_get_uint8(v_val_5044_, sizeof(void*)*3);
lean_dec_ref(v_val_5044_);
v___x_5049_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5045_, v_rhs_5046_, v_proof_5047_, v_isHEq_5048_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_dec_ref(v___x_5049_);
goto _start;
}
else
{
lean_object* v_a_5051_; lean_object* v___x_5053_; uint8_t v_isShared_5054_; uint8_t v_isSharedCheck_5058_; 
v_a_5051_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5058_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5058_ == 0)
{
v___x_5053_ = v___x_5049_;
v_isShared_5054_ = v_isSharedCheck_5058_;
goto v_resetjp_5052_;
}
else
{
lean_inc(v_a_5051_);
lean_dec(v___x_5049_);
v___x_5053_ = lean_box(0);
v_isShared_5054_ = v_isSharedCheck_5058_;
goto v_resetjp_5052_;
}
v_resetjp_5052_:
{
lean_object* v___x_5056_; 
if (v_isShared_5054_ == 0)
{
v___x_5056_ = v___x_5053_;
goto v_reusejp_5055_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_a_5051_);
v___x_5056_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5055_;
}
v_reusejp_5055_:
{
return v___x_5056_;
}
}
}
}
else
{
lean_object* v_prop_5059_; lean_object* v_proof_5060_; lean_object* v_generation_5061_; lean_object* v___x_5062_; 
v_prop_5059_ = lean_ctor_get(v_val_5044_, 0);
lean_inc_ref(v_prop_5059_);
v_proof_5060_ = lean_ctor_get(v_val_5044_, 1);
lean_inc_ref(v_proof_5060_);
v_generation_5061_ = lean_ctor_get(v_val_5044_, 2);
lean_inc(v_generation_5061_);
lean_dec_ref(v_val_5044_);
v___x_5062_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5059_, v_proof_5060_, v_generation_5061_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
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
}
else
{
lean_object* v___x_5072_; lean_object* v___x_5074_; 
lean_dec(v_a_5040_);
v___x_5072_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5072_);
v___x_5074_ = v___x_5042_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v___x_5072_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
v_a_5077_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5039_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5039_);
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
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
v_a_5085_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5038_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5038_);
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
else
{
lean_object* v___x_5093_; 
v___x_5093_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5023_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5101_; 
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5101_ == 0)
{
lean_object* v_unused_5102_; 
v_unused_5102_ = lean_ctor_get(v___x_5093_, 0);
lean_dec(v_unused_5102_);
v___x_5095_ = v___x_5093_;
v_isShared_5096_ = v_isSharedCheck_5101_;
goto v_resetjp_5094_;
}
else
{
lean_dec(v___x_5093_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5101_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5097_; lean_object* v___x_5099_; 
v___x_5097_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 0, v___x_5097_);
v___x_5099_ = v___x_5095_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5097_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
v_a_5103_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_5093_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_5093_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
v_a_5111_ = lean_ctor_get(v___x_5034_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5034_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_5034_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5034_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec(v___y_5119_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_){
_start:
{
lean_object* v___x_5142_; 
v___x_5142_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_);
lean_dec(v_a_5140_);
lean_dec_ref(v_a_5139_);
lean_dec(v_a_5138_);
lean_dec_ref(v_a_5137_);
lean_dec(v_a_5136_);
lean_dec_ref(v_a_5135_);
lean_dec(v_a_5134_);
lean_dec_ref(v_a_5133_);
lean_dec(v_a_5132_);
lean_dec(v_a_5131_);
if (lean_obj_tag(v___x_5142_) == 0)
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5156_; 
v_a_5143_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5145_ = v___x_5142_;
v_isShared_5146_ = v_isSharedCheck_5156_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5142_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5156_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v_fst_5147_; 
v_fst_5147_ = lean_ctor_get(v_a_5143_, 0);
lean_inc(v_fst_5147_);
lean_dec(v_a_5143_);
if (lean_obj_tag(v_fst_5147_) == 0)
{
lean_object* v___x_5148_; lean_object* v___x_5150_; 
v___x_5148_ = lean_box(0);
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 0, v___x_5148_);
v___x_5150_ = v___x_5145_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v___x_5148_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
else
{
lean_object* v_val_5152_; lean_object* v___x_5154_; 
v_val_5152_ = lean_ctor_get(v_fst_5147_, 0);
lean_inc(v_val_5152_);
lean_dec_ref(v_fst_5147_);
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 0, v_val_5152_);
v___x_5154_ = v___x_5145_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_val_5152_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
v_a_5157_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5142_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5142_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = lean_grind_process_new_facts(v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_b_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
lean_object* v___x_5189_; 
v___x_5189_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
return v___x_5189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_b_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_){
_start:
{
lean_object* v_res_5202_; 
v_res_5202_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_b_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
lean_dec(v___y_5200_);
lean_dec_ref(v___y_5199_);
lean_dec(v___y_5198_);
lean_dec_ref(v___y_5197_);
lean_dec(v___y_5196_);
lean_dec_ref(v___y_5195_);
lean_dec(v___y_5194_);
lean_dec_ref(v___y_5193_);
lean_dec(v___y_5192_);
lean_dec(v___y_5191_);
lean_dec_ref(v_b_5190_);
return v_res_5202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5203_, lean_object* v_proof_5204_, lean_object* v_generation_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_){
_start:
{
uint8_t v___x_5217_; 
lean_inc_ref(v_fact_5203_);
v___x_5217_ = l_Lean_Expr_isTrue(v_fact_5203_);
if (v___x_5217_ == 0)
{
lean_object* v___x_5218_; 
v___x_5218_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5206_);
if (lean_obj_tag(v___x_5218_) == 0)
{
lean_object* v_a_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5230_; 
v_a_5219_ = lean_ctor_get(v___x_5218_, 0);
v_isSharedCheck_5230_ = !lean_is_exclusive(v___x_5218_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_5221_ = v___x_5218_;
v_isShared_5222_ = v_isSharedCheck_5230_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_a_5219_);
lean_dec(v___x_5218_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5230_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
uint8_t v___x_5223_; 
v___x_5223_ = lean_unbox(v_a_5219_);
lean_dec(v_a_5219_);
if (v___x_5223_ == 0)
{
lean_object* v___x_5224_; lean_object* v___x_5225_; 
lean_del_object(v___x_5221_);
v___x_5224_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5206_);
lean_dec_ref(v___x_5224_);
v___x_5225_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5203_, v_proof_5204_, v_generation_5205_, v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_);
return v___x_5225_;
}
else
{
lean_object* v___x_5226_; lean_object* v___x_5228_; 
lean_dec(v_generation_5205_);
lean_dec_ref(v_proof_5204_);
lean_dec_ref(v_fact_5203_);
v___x_5226_ = lean_box(0);
if (v_isShared_5222_ == 0)
{
lean_ctor_set(v___x_5221_, 0, v___x_5226_);
v___x_5228_ = v___x_5221_;
goto v_reusejp_5227_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v___x_5226_);
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
lean_dec(v_generation_5205_);
lean_dec_ref(v_proof_5204_);
lean_dec_ref(v_fact_5203_);
v_a_5231_ = lean_ctor_get(v___x_5218_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5218_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5233_ = v___x_5218_;
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5218_);
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
lean_object* v___x_5239_; lean_object* v___x_5240_; 
lean_dec(v_generation_5205_);
lean_dec_ref(v_proof_5204_);
lean_dec_ref(v_fact_5203_);
v___x_5239_ = lean_box(0);
v___x_5240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5240_, 0, v___x_5239_);
return v___x_5240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5241_, lean_object* v_proof_5242_, lean_object* v_generation_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_){
_start:
{
lean_object* v_res_5255_; 
v_res_5255_ = l_Lean_Meta_Grind_add(v_fact_5241_, v_proof_5242_, v_generation_5243_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_);
lean_dec(v_a_5253_);
lean_dec_ref(v_a_5252_);
lean_dec(v_a_5251_);
lean_dec_ref(v_a_5250_);
lean_dec(v_a_5249_);
lean_dec_ref(v_a_5248_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_a_5245_);
lean_dec(v_a_5244_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5256_, lean_object* v_generation_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_){
_start:
{
lean_object* v___x_5269_; 
lean_inc(v_fvarId_5256_);
v___x_5269_ = l_Lean_FVarId_getType___redArg(v_fvarId_5256_, v_a_5264_, v_a_5266_, v_a_5267_);
if (lean_obj_tag(v___x_5269_) == 0)
{
lean_object* v_a_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; 
v_a_5270_ = lean_ctor_get(v___x_5269_, 0);
lean_inc(v_a_5270_);
lean_dec_ref(v___x_5269_);
v___x_5271_ = l_Lean_mkFVar(v_fvarId_5256_);
v___x_5272_ = l_Lean_Meta_Grind_add(v_a_5270_, v___x_5271_, v_generation_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_);
return v___x_5272_;
}
else
{
lean_object* v_a_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5280_; 
lean_dec(v_generation_5257_);
lean_dec(v_fvarId_5256_);
v_a_5273_ = lean_ctor_get(v___x_5269_, 0);
v_isSharedCheck_5280_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5280_ == 0)
{
v___x_5275_ = v___x_5269_;
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_a_5273_);
lean_dec(v___x_5269_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5281_, lean_object* v_generation_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5281_, v_generation_5282_, v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_);
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
return v_res_5294_;
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
