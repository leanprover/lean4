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
size_t lean_usize_sub(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* v___x_274_, lean_object* v_x_275_, size_t v_x_276_, lean_object* v_x_277_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
lean_object* v_es_278_; lean_object* v___x_279_; size_t v___x_280_; size_t v___x_281_; lean_object* v_j_282_; lean_object* v_entry_283_; 
v_es_278_ = lean_ctor_get(v_x_275_, 0);
v___x_279_ = lean_box(2);
v___x_280_ = ((size_t)31ULL);
v___x_281_ = lean_usize_land(v_x_276_, v___x_280_);
v_j_282_ = lean_usize_to_nat(v___x_281_);
v_entry_283_ = lean_array_get(v___x_279_, v_es_278_, v_j_282_);
switch(lean_obj_tag(v_entry_283_))
{
case 0:
{
lean_object* v_key_284_; uint8_t v___x_285_; 
v_key_284_ = lean_ctor_get(v_entry_283_, 0);
lean_inc(v_key_284_);
lean_dec_ref_known(v_entry_283_, 2);
v___x_285_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_274_, v_x_277_, v_key_284_);
if (v___x_285_ == 0)
{
lean_dec(v_j_282_);
return v_x_275_;
}
else
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
lean_inc_ref(v_es_278_);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_x_275_, 0);
lean_dec(v_unused_294_);
v___x_287_ = v_x_275_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_x_275_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = lean_array_set(v_es_278_, v_j_282_, v___x_279_);
lean_dec(v_j_282_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_289_);
v___x_291_ = v___x_287_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
case 1:
{
lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_329_; 
lean_inc_ref(v_es_278_);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_x_275_, 0);
lean_dec(v_unused_330_);
v___x_296_ = v_x_275_;
v_isShared_297_ = v_isSharedCheck_329_;
goto v_resetjp_295_;
}
else
{
lean_dec(v_x_275_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_329_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_node_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_328_; 
v_node_298_ = lean_ctor_get(v_entry_283_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_entry_283_);
if (v_isSharedCheck_328_ == 0)
{
v___x_300_ = v_entry_283_;
v_isShared_301_ = v_isSharedCheck_328_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_node_298_);
lean_dec(v_entry_283_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_328_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
size_t v___x_302_; lean_object* v_entries_303_; size_t v___x_304_; lean_object* v_newNode_305_; lean_object* v___x_306_; 
v___x_302_ = ((size_t)5ULL);
v_entries_303_ = lean_array_set(v_es_278_, v_j_282_, v___x_279_);
v___x_304_ = lean_usize_shift_right(v_x_276_, v___x_302_);
v_newNode_305_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_274_, v_node_298_, v___x_304_, v_x_277_);
lean_inc_ref(v_newNode_305_);
v___x_306_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_305_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_308_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v_newNode_305_);
v___x_308_ = v___x_300_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_newNode_305_);
v___x_308_ = v_reuseFailAlloc_313_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_array_set(v_entries_303_, v_j_282_, v___x_308_);
lean_dec(v_j_282_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_309_);
v___x_311_ = v___x_296_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
else
{
lean_object* v_val_314_; lean_object* v_fst_315_; lean_object* v_snd_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_newNode_305_);
lean_del_object(v___x_300_);
v_val_314_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_val_314_);
lean_dec_ref_known(v___x_306_, 1);
v_fst_315_ = lean_ctor_get(v_val_314_, 0);
v_snd_316_ = lean_ctor_get(v_val_314_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_val_314_);
if (v_isSharedCheck_327_ == 0)
{
v___x_318_ = v_val_314_;
v_isShared_319_ = v_isSharedCheck_327_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_snd_316_);
lean_inc(v_fst_315_);
lean_dec(v_val_314_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_327_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_fst_315_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_snd_316_);
v___x_321_ = v_reuseFailAlloc_326_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_array_set(v_entries_303_, v_j_282_, v___x_321_);
lean_dec(v_j_282_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_322_);
v___x_324_ = v___x_296_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_282_);
lean_dec_ref(v_x_277_);
return v_x_275_;
}
}
}
else
{
lean_object* v_ks_331_; lean_object* v_vs_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_346_; 
v_ks_331_ = lean_ctor_get(v_x_275_, 0);
v_vs_332_ = lean_ctor_get(v_x_275_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_275_);
if (v_isSharedCheck_346_ == 0)
{
v___x_334_ = v_x_275_;
v_isShared_335_ = v_isSharedCheck_346_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_vs_332_);
lean_inc(v_ks_331_);
lean_dec(v_x_275_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_346_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; 
v___x_336_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_274_, v_ks_331_, v_x_277_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v___x_338_; 
if (v_isShared_335_ == 0)
{
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_ks_331_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_vs_332_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
else
{
lean_object* v_val_340_; lean_object* v_keys_x27_341_; lean_object* v_vals_x27_342_; lean_object* v___x_344_; 
v_val_340_ = lean_ctor_get(v___x_336_, 0);
lean_inc_n(v_val_340_, 2);
lean_dec_ref_known(v___x_336_, 1);
v_keys_x27_341_ = l_Array_eraseIdx___redArg(v_ks_331_, v_val_340_);
v_vals_x27_342_ = l_Array_eraseIdx___redArg(v_vs_332_, v_val_340_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v_vals_x27_342_);
lean_ctor_set(v___x_334_, 0, v_keys_x27_341_);
v___x_344_ = v___x_334_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_keys_x27_341_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_vals_x27_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* v___x_347_, lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
size_t v_x_28233__boxed_351_; lean_object* v_res_352_; 
v_x_28233__boxed_351_ = lean_unbox_usize(v_x_349_);
lean_dec(v_x_349_);
v_res_352_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_347_, v_x_348_, v_x_28233__boxed_351_, v_x_350_);
lean_dec_ref(v___x_347_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint64_t v___x_356_; size_t v_h_357_; lean_object* v___x_358_; 
lean_inc_ref(v_x_355_);
v___x_356_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_353_, v_x_355_);
v_h_357_ = lean_uint64_to_usize(v___x_356_);
v___x_358_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_353_, v_x_354_, v_h_357_, v_x_355_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg___boxed(lean_object* v___x_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_359_, v_x_360_, v_x_361_);
lean_dec_ref(v___x_359_);
return v_res_362_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_374_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_375_ = l_Lean_Name_append(v___x_374_, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object* v_as_x27_379_, lean_object* v_b_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
if (lean_obj_tag(v_as_x27_379_) == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v_b_380_);
return v___x_392_;
}
else
{
lean_object* v_head_393_; lean_object* v_tail_394_; lean_object* v___x_395_; lean_object* v___y_397_; uint8_t v_a_437_; uint8_t v___x_450_; 
v_head_393_ = lean_ctor_get(v_as_x27_379_, 0);
v_tail_394_ = lean_ctor_get(v_as_x27_379_, 1);
v___x_395_ = lean_box(0);
v___x_450_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_393_);
if (v___x_450_ == 0)
{
v_a_437_ = v___x_450_;
goto v___jp_436_;
}
else
{
lean_object* v___x_451_; 
lean_inc(v_head_393_);
v___x_451_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_393_, v___y_381_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; uint8_t v___x_453_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v___x_453_ = lean_unbox(v_a_452_);
lean_dec(v_a_452_);
v_a_437_ = v___x_453_;
goto v___jp_436_;
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_a_454_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_451_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_451_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
v___jp_396_:
{
lean_object* v___x_398_; lean_object* v_toGoalState_399_; lean_object* v_mvarId_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_435_; 
v___x_398_ = lean_st_ref_take(v___y_397_);
v_toGoalState_399_ = lean_ctor_get(v___x_398_, 0);
v_mvarId_400_ = lean_ctor_get(v___x_398_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_435_ == 0)
{
v___x_402_ = v___x_398_;
v_isShared_403_ = v_isSharedCheck_435_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_mvarId_400_);
lean_inc(v_toGoalState_399_);
lean_dec(v___x_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_435_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v_nextDeclIdx_404_; lean_object* v_enodeMap_405_; lean_object* v_exprs_406_; lean_object* v_parents_407_; lean_object* v_congrTable_408_; lean_object* v_appMap_409_; lean_object* v_indicesFound_410_; lean_object* v_newFacts_411_; uint8_t v_inconsistent_412_; lean_object* v_nextIdx_413_; lean_object* v_newRawFacts_414_; lean_object* v_facts_415_; lean_object* v_extThms_416_; lean_object* v_ematch_417_; lean_object* v_inj_418_; lean_object* v_split_419_; lean_object* v_clean_420_; lean_object* v_sstates_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_434_; 
v_nextDeclIdx_404_ = lean_ctor_get(v_toGoalState_399_, 0);
v_enodeMap_405_ = lean_ctor_get(v_toGoalState_399_, 1);
v_exprs_406_ = lean_ctor_get(v_toGoalState_399_, 2);
v_parents_407_ = lean_ctor_get(v_toGoalState_399_, 3);
v_congrTable_408_ = lean_ctor_get(v_toGoalState_399_, 4);
v_appMap_409_ = lean_ctor_get(v_toGoalState_399_, 5);
v_indicesFound_410_ = lean_ctor_get(v_toGoalState_399_, 6);
v_newFacts_411_ = lean_ctor_get(v_toGoalState_399_, 7);
v_inconsistent_412_ = lean_ctor_get_uint8(v_toGoalState_399_, sizeof(void*)*17);
v_nextIdx_413_ = lean_ctor_get(v_toGoalState_399_, 8);
v_newRawFacts_414_ = lean_ctor_get(v_toGoalState_399_, 9);
v_facts_415_ = lean_ctor_get(v_toGoalState_399_, 10);
v_extThms_416_ = lean_ctor_get(v_toGoalState_399_, 11);
v_ematch_417_ = lean_ctor_get(v_toGoalState_399_, 12);
v_inj_418_ = lean_ctor_get(v_toGoalState_399_, 13);
v_split_419_ = lean_ctor_get(v_toGoalState_399_, 14);
v_clean_420_ = lean_ctor_get(v_toGoalState_399_, 15);
v_sstates_421_ = lean_ctor_get(v_toGoalState_399_, 16);
v_isSharedCheck_434_ = !lean_is_exclusive(v_toGoalState_399_);
if (v_isSharedCheck_434_ == 0)
{
v___x_423_ = v_toGoalState_399_;
v_isShared_424_ = v_isSharedCheck_434_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_sstates_421_);
lean_inc(v_clean_420_);
lean_inc(v_split_419_);
lean_inc(v_inj_418_);
lean_inc(v_ematch_417_);
lean_inc(v_extThms_416_);
lean_inc(v_facts_415_);
lean_inc(v_newRawFacts_414_);
lean_inc(v_nextIdx_413_);
lean_inc(v_newFacts_411_);
lean_inc(v_indicesFound_410_);
lean_inc(v_appMap_409_);
lean_inc(v_congrTable_408_);
lean_inc(v_parents_407_);
lean_inc(v_exprs_406_);
lean_inc(v_enodeMap_405_);
lean_inc(v_nextDeclIdx_404_);
lean_dec(v_toGoalState_399_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_434_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
lean_inc(v_head_393_);
v___x_425_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_405_, v_congrTable_408_, v_head_393_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_nextDeclIdx_404_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_enodeMap_405_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_exprs_406_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_parents_407_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_433_, 5, v_appMap_409_);
lean_ctor_set(v_reuseFailAlloc_433_, 6, v_indicesFound_410_);
lean_ctor_set(v_reuseFailAlloc_433_, 7, v_newFacts_411_);
lean_ctor_set(v_reuseFailAlloc_433_, 8, v_nextIdx_413_);
lean_ctor_set(v_reuseFailAlloc_433_, 9, v_newRawFacts_414_);
lean_ctor_set(v_reuseFailAlloc_433_, 10, v_facts_415_);
lean_ctor_set(v_reuseFailAlloc_433_, 11, v_extThms_416_);
lean_ctor_set(v_reuseFailAlloc_433_, 12, v_ematch_417_);
lean_ctor_set(v_reuseFailAlloc_433_, 13, v_inj_418_);
lean_ctor_set(v_reuseFailAlloc_433_, 14, v_split_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 15, v_clean_420_);
lean_ctor_set(v_reuseFailAlloc_433_, 16, v_sstates_421_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*17, v_inconsistent_412_);
v___x_427_ = v_reuseFailAlloc_433_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_429_; 
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_427_);
v___x_429_ = v___x_402_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_mvarId_400_);
v___x_429_ = v_reuseFailAlloc_432_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; 
v___x_430_ = lean_st_ref_set(v___y_397_, v___x_429_);
v_as_x27_379_ = v_tail_394_;
v_b_380_ = v___x_395_;
goto _start;
}
}
}
}
}
v___jp_436_:
{
if (v_a_437_ == 0)
{
v_as_x27_379_ = v_tail_394_;
v_b_380_ = v___x_395_;
goto _start;
}
else
{
lean_object* v_options_439_; uint8_t v_hasTrace_440_; 
v_options_439_ = lean_ctor_get(v___y_389_, 2);
v_hasTrace_440_ = lean_ctor_get_uint8(v_options_439_, sizeof(void*)*1);
if (v_hasTrace_440_ == 0)
{
v___y_397_ = v___y_381_;
goto v___jp_396_;
}
else
{
lean_object* v_inheritedTraceOptions_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_inheritedTraceOptions_441_ = lean_ctor_get(v___y_389_, 13);
v___x_442_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_443_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_444_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_441_, v_options_439_, v___x_443_);
if (v___x_444_ == 0)
{
v___y_397_ = v___y_381_;
goto v___jp_396_;
}
else
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Grind_updateLastTag(v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref_known(v___x_445_, 1);
v___x_446_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_393_);
v___x_447_ = l_Lean_MessageData_ofExpr(v_head_393_);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_442_, v___x_448_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_dec_ref_known(v___x_449_, 1);
v___y_397_ = v___y_381_;
goto v___jp_396_;
}
else
{
return v___x_449_;
}
}
else
{
return v___x_445_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_462_, v_b_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec(v___y_464_);
lean_dec(v_as_x27_462_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_getParents___redArg(v_root_476_, v_a_477_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v___x_490_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_489_);
v___x_491_ = lean_box(0);
v___x_492_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_490_, v___x_491_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
lean_dec(v___x_490_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v___x_492_, 0);
lean_dec(v_unused_500_);
v___x_494_ = v___x_492_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_dec(v___x_492_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v_a_489_);
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_489_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_a_489_);
v_a_501_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_492_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_492_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_root_509_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_522_, lean_object* v_00_u03b2_523_, lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_522_, v_x_524_, v_x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_527_, lean_object* v_00_u03b2_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_527_, v_00_u03b2_528_, v_x_529_, v_x_530_);
lean_dec_ref(v___x_527_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_532_, lean_object* v_msg_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_532_, v_msg_533_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_546_, lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_546_, v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec(v___y_548_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_560_, lean_object* v_as_x27_561_, lean_object* v_b_562_, lean_object* v_a_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_561_, v_b_562_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_576_, lean_object* v_as_x27_577_, lean_object* v_b_578_, lean_object* v_a_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_576_, v_as_x27_577_, v_b_578_, v_a_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec(v___y_580_);
lean_dec(v_as_x27_577_);
lean_dec(v_as_576_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_592_, lean_object* v_00_u03b2_593_, lean_object* v_x_594_, size_t v_x_595_, lean_object* v_x_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_592_, v_x_594_, v_x_595_, v_x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_598_, lean_object* v_00_u03b2_599_, lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
size_t v_x_28695__boxed_603_; lean_object* v_res_604_; 
v_x_28695__boxed_603_ = lean_unbox_usize(v_x_601_);
lean_dec(v_x_601_);
v_res_604_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_598_, v_00_u03b2_599_, v_x_600_, v_x_28695__boxed_603_, v_x_602_);
lean_dec_ref(v___x_598_);
return v_res_604_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_607_ = l_Lean_stringToMessageData(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_608_, lean_object* v_b_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
if (lean_obj_tag(v_as_x27_608_) == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v_b_609_);
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v___x_624_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; uint8_t v_a_639_; uint8_t v___x_652_; 
v_head_622_ = lean_ctor_get(v_as_x27_608_, 0);
v_tail_623_ = lean_ctor_get(v_as_x27_608_, 1);
v___x_624_ = lean_box(0);
v___x_652_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_622_);
if (v___x_652_ == 0)
{
v_a_639_ = v___x_652_;
goto v___jp_638_;
}
else
{
lean_object* v___x_653_; 
lean_inc(v_head_622_);
v___x_653_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_622_, v___y_610_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; uint8_t v___x_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = lean_unbox(v_a_654_);
lean_dec(v_a_654_);
v_a_639_ = v___x_655_;
goto v___jp_638_;
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_653_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_653_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
v___jp_625_:
{
lean_object* v___x_636_; 
lean_inc(v_head_622_);
v___x_636_ = l_Lean_Meta_Grind_addCongrTable(v_head_622_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_dec_ref_known(v___x_636_, 1);
v_as_x27_608_ = v_tail_623_;
v_b_609_ = v___x_624_;
goto _start;
}
else
{
return v___x_636_;
}
}
v___jp_638_:
{
if (v_a_639_ == 0)
{
v_as_x27_608_ = v_tail_623_;
v_b_609_ = v___x_624_;
goto _start;
}
else
{
lean_object* v_options_641_; uint8_t v_hasTrace_642_; 
v_options_641_ = lean_ctor_get(v___y_618_, 2);
v_hasTrace_642_ = lean_ctor_get_uint8(v_options_641_, sizeof(void*)*1);
if (v_hasTrace_642_ == 0)
{
v___y_626_ = v___y_610_;
v___y_627_ = v___y_611_;
v___y_628_ = v___y_612_;
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
goto v___jp_625_;
}
else
{
lean_object* v_inheritedTraceOptions_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_inheritedTraceOptions_643_ = lean_ctor_get(v___y_618_, 13);
v___x_644_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_645_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_646_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_643_, v_options_641_, v___x_645_);
if (v___x_646_ == 0)
{
v___y_626_ = v___y_610_;
v___y_627_ = v___y_611_;
v___y_628_ = v___y_612_;
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
goto v___jp_625_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_Grind_updateLastTag(v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
lean_dec_ref_known(v___x_647_, 1);
v___x_648_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_622_);
v___x_649_ = l_Lean_MessageData_ofExpr(v_head_622_);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_644_, v___x_650_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_dec_ref_known(v___x_651_, 1);
v___y_626_ = v___y_610_;
v___y_627_ = v___y_611_;
v___y_628_ = v___y_612_;
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
goto v___jp_625_;
}
else
{
return v___x_651_;
}
}
else
{
return v___x_647_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_664_, lean_object* v_b_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_664_, v_b_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec(v___y_666_);
lean_dec(v_as_x27_664_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_678_);
v___x_691_ = lean_box(0);
v___x_692_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_690_, v___x_691_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
lean_dec(v___x_690_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v___x_692_, 0);
lean_dec(v_unused_700_);
v___x_694_ = v___x_692_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_dec(v___x_692_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_691_);
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_691_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
else
{
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec(v_a_702_);
lean_dec(v_parents_701_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_714_, lean_object* v_as_x27_715_, lean_object* v_b_716_, lean_object* v_a_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_715_, v_b_716_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_730_, lean_object* v_as_x27_731_, lean_object* v_b_732_, lean_object* v_a_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_730_, v_as_x27_731_, v_b_732_, v_a_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec(v___y_734_);
lean_dec(v_as_x27_731_);
lean_dec(v_as_730_);
return v_res_745_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_746_, lean_object* v_i_747_, lean_object* v_k_748_){
_start:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_array_get_size(v_keys_746_);
v___x_750_ = lean_nat_dec_lt(v_i_747_, v___x_749_);
if (v___x_750_ == 0)
{
lean_dec(v_i_747_);
return v___x_750_;
}
else
{
lean_object* v_k_x27_751_; uint8_t v___x_752_; 
v_k_x27_751_ = lean_array_fget_borrowed(v_keys_746_, v_i_747_);
v___x_752_ = l_Lean_instBEqMVarId_beq(v_k_748_, v_k_x27_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_i_747_, v___x_753_);
lean_dec(v_i_747_);
v_i_747_ = v___x_754_;
goto _start;
}
else
{
lean_dec(v_i_747_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_756_, lean_object* v_i_757_, lean_object* v_k_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_756_, v_i_757_, v_k_758_);
lean_dec(v_k_758_);
lean_dec_ref(v_keys_756_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_761_, size_t v_x_762_, lean_object* v_x_763_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_object* v_es_764_; lean_object* v___x_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v_j_768_; lean_object* v___x_769_; 
v_es_764_ = lean_ctor_get(v_x_761_, 0);
v___x_765_ = lean_box(2);
v___x_766_ = ((size_t)31ULL);
v___x_767_ = lean_usize_land(v_x_762_, v___x_766_);
v_j_768_ = lean_usize_to_nat(v___x_767_);
v___x_769_ = lean_array_get_borrowed(v___x_765_, v_es_764_, v_j_768_);
lean_dec(v_j_768_);
switch(lean_obj_tag(v___x_769_))
{
case 0:
{
lean_object* v_key_770_; uint8_t v___x_771_; 
v_key_770_ = lean_ctor_get(v___x_769_, 0);
v___x_771_ = l_Lean_instBEqMVarId_beq(v_x_763_, v_key_770_);
return v___x_771_;
}
case 1:
{
lean_object* v_node_772_; size_t v___x_773_; size_t v___x_774_; 
v_node_772_ = lean_ctor_get(v___x_769_, 0);
v___x_773_ = ((size_t)5ULL);
v___x_774_ = lean_usize_shift_right(v_x_762_, v___x_773_);
v_x_761_ = v_node_772_;
v_x_762_ = v___x_774_;
goto _start;
}
default: 
{
uint8_t v___x_776_; 
v___x_776_ = 0;
return v___x_776_;
}
}
}
else
{
lean_object* v_ks_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v_ks_777_ = lean_ctor_get(v_x_761_, 0);
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_777_, v___x_778_, v_x_763_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
size_t v_x_10232__boxed_783_; uint8_t v_res_784_; lean_object* v_r_785_; 
v_x_10232__boxed_783_ = lean_unbox_usize(v_x_781_);
lean_dec(v_x_781_);
v_res_784_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_780_, v_x_10232__boxed_783_, v_x_782_);
lean_dec(v_x_782_);
lean_dec_ref(v_x_780_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
uint64_t v___x_788_; size_t v___x_789_; uint8_t v___x_790_; 
v___x_788_ = l_Lean_instHashableMVarId_hash(v_x_787_);
v___x_789_ = lean_uint64_to_usize(v___x_788_);
v___x_790_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_786_, v___x_789_, v_x_787_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_791_, v_x_792_);
lean_dec(v_x_792_);
lean_dec_ref(v_x_791_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; lean_object* v_mctx_799_; lean_object* v_eAssignment_800_; uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_798_ = lean_st_ref_get(v___y_796_);
v_mctx_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc_ref(v_mctx_799_);
lean_dec(v___x_798_);
v_eAssignment_800_ = lean_ctor_get(v_mctx_799_, 8);
lean_inc_ref(v_eAssignment_800_);
lean_dec_ref(v_mctx_799_);
v___x_801_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_800_, v_mvarId_795_);
lean_dec_ref(v_eAssignment_800_);
v___x_802_ = lean_box(v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec(v_mvarId_804_);
return v_res_807_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_818_ = l_Lean_mkConst(v___x_817_, v___x_816_);
return v___x_818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = lean_box(0);
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_826_ = l_Lean_mkConst(v___x_825_, v___x_824_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v___x_838_; lean_object* v_mvarId_839_; lean_object* v___x_840_; lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_894_; 
v___x_838_ = lean_st_ref_get(v_a_827_);
v_mvarId_839_ = lean_ctor_get(v___x_838_, 1);
lean_inc(v_mvarId_839_);
lean_dec(v___x_838_);
v___x_840_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_839_, v_a_834_);
lean_dec(v_mvarId_839_);
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_894_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_894_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_894_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
uint8_t v___x_845_; 
v___x_845_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
lean_del_object(v___x_843_);
v___x_846_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_831_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_847_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_850_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_831_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_831_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_855_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_856_ = l_Lean_mkApp4(v___x_854_, v_a_851_, v_a_853_, v_a_849_, v___x_855_);
v___x_857_ = l_Lean_Meta_Grind_closeGoal(v___x_856_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
return v___x_857_;
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_a_851_);
lean_dec(v_a_849_);
v_a_858_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_852_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_852_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_849_);
v_a_866_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_850_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_850_);
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
v_a_874_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_848_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_848_);
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
v_a_882_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_846_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_846_);
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
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_box(0);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_890_);
v___x_892_ = v___x_843_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec(v_a_895_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_907_, v___y_915_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec(v___y_921_);
lean_dec(v_mvarId_920_);
return v_res_932_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_933_, lean_object* v_x_934_, lean_object* v_x_935_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_934_, v_x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
uint8_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_937_, v_x_938_, v_x_939_);
lean_dec(v_x_939_);
lean_dec_ref(v_x_938_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_942_, lean_object* v_x_943_, size_t v_x_944_, lean_object* v_x_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_943_, v_x_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
size_t v_x_10515__boxed_951_; uint8_t v_res_952_; lean_object* v_r_953_; 
v_x_10515__boxed_951_ = lean_unbox_usize(v_x_949_);
lean_dec(v_x_949_);
v_res_952_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_947_, v_x_948_, v_x_10515__boxed_951_, v_x_950_);
lean_dec(v_x_950_);
lean_dec_ref(v_x_948_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_954_, lean_object* v_keys_955_, lean_object* v_vals_956_, lean_object* v_heq_957_, lean_object* v_i_958_, lean_object* v_k_959_){
_start:
{
uint8_t v___x_960_; 
v___x_960_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_955_, v_i_958_, v_k_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_961_, lean_object* v_keys_962_, lean_object* v_vals_963_, lean_object* v_heq_964_, lean_object* v_i_965_, lean_object* v_k_966_){
_start:
{
uint8_t v_res_967_; lean_object* v_r_968_; 
v_res_967_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_961_, v_keys_962_, v_vals_963_, v_heq_964_, v_i_965_, v_k_966_);
lean_dec(v_k_966_);
lean_dec_ref(v_vals_963_);
lean_dec_ref(v_keys_962_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_box(0);
v___x_973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_974_ = l_Lean_mkConst(v___x_973_, v___x_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_975_, lean_object* v_rhs_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; 
lean_inc_ref(v_rhs_976_);
lean_inc_ref(v_lhs_975_);
v___x_988_ = l_Lean_Meta_mkEq(v_lhs_975_, v_rhs_976_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
lean_inc(v_a_986_);
lean_inc_ref(v_a_985_);
lean_inc(v_a_984_);
lean_inc_ref(v_a_983_);
lean_inc(v_a_982_);
lean_inc_ref(v_a_981_);
lean_inc(v_a_980_);
lean_inc_ref(v_a_979_);
lean_inc(v_a_978_);
lean_inc(v_a_977_);
v___x_990_ = lean_grind_mk_eq_proof(v_lhs_975_, v_rhs_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
lean_inc(v_a_989_);
v___x_992_ = l_Lean_Meta_mkDecide(v_a_989_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_981_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v___x_996_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_997_ = l_Lean_Expr_appArg_x21(v_a_993_);
lean_dec(v_a_993_);
v___x_998_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_989_);
v___x_999_ = l_Lean_mkApp3(v___x_996_, v_a_989_, v___x_997_, v___x_998_);
v___x_1000_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1001_ = l_Lean_mkApp4(v___x_1000_, v_a_989_, v_a_995_, v___x_999_, v_a_991_);
v___x_1002_ = l_Lean_Meta_Grind_closeGoal(v___x_1001_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
return v___x_1002_;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec(v_a_993_);
lean_dec(v_a_991_);
lean_dec(v_a_989_);
v_a_1003_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_994_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_994_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec(v_a_991_);
lean_dec(v_a_989_);
v_a_1011_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_992_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_992_);
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
lean_dec(v_a_989_);
v_a_1019_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_990_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_990_);
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
lean_dec_ref(v_rhs_976_);
lean_dec_ref(v_lhs_975_);
v_a_1027_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_988_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_988_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1035_, lean_object* v_rhs_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1035_, v_rhs_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec(v_a_1037_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1049_, lean_object* v_as_x27_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
if (lean_obj_tag(v_as_x27_1050_) == 0)
{
lean_object* v___x_1063_; 
lean_dec(v___x_1049_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_b_1051_);
return v___x_1063_;
}
else
{
lean_object* v_head_1064_; lean_object* v_tail_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_head_1064_ = lean_ctor_get(v_as_x27_1050_, 0);
v_tail_1065_ = lean_ctor_get(v_as_x27_1050_, 1);
v___x_1066_ = lean_st_ref_get(v___y_1052_);
lean_inc(v_head_1064_);
v___x_1067_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1066_, v_head_1064_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v_self_1069_; lean_object* v_next_1070_; lean_object* v_root_1071_; lean_object* v_congr_1072_; lean_object* v_target_x3f_1073_; lean_object* v_proof_x3f_1074_; uint8_t v_flipped_1075_; lean_object* v_size_1076_; uint8_t v_interpreted_1077_; uint8_t v_ctor_1078_; uint8_t v_hasLambdas_1079_; uint8_t v_heqProofs_1080_; lean_object* v_idx_1081_; lean_object* v_generation_1082_; lean_object* v_mt_1083_; lean_object* v_sTerms_1084_; uint8_t v_funCC_1085_; lean_object* v_ematchDiagSource_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1099_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v_self_1069_ = lean_ctor_get(v_a_1068_, 0);
v_next_1070_ = lean_ctor_get(v_a_1068_, 1);
v_root_1071_ = lean_ctor_get(v_a_1068_, 2);
v_congr_1072_ = lean_ctor_get(v_a_1068_, 3);
v_target_x3f_1073_ = lean_ctor_get(v_a_1068_, 4);
v_proof_x3f_1074_ = lean_ctor_get(v_a_1068_, 5);
v_flipped_1075_ = lean_ctor_get_uint8(v_a_1068_, sizeof(void*)*12);
v_size_1076_ = lean_ctor_get(v_a_1068_, 6);
v_interpreted_1077_ = lean_ctor_get_uint8(v_a_1068_, sizeof(void*)*12 + 1);
v_ctor_1078_ = lean_ctor_get_uint8(v_a_1068_, sizeof(void*)*12 + 2);
v_hasLambdas_1079_ = lean_ctor_get_uint8(v_a_1068_, sizeof(void*)*12 + 3);
v_heqProofs_1080_ = lean_ctor_get_uint8(v_a_1068_, sizeof(void*)*12 + 4);
v_idx_1081_ = lean_ctor_get(v_a_1068_, 7);
v_generation_1082_ = lean_ctor_get(v_a_1068_, 8);
v_mt_1083_ = lean_ctor_get(v_a_1068_, 9);
v_sTerms_1084_ = lean_ctor_get(v_a_1068_, 10);
v_funCC_1085_ = lean_ctor_get_uint8(v_a_1068_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1086_ = lean_ctor_get(v_a_1068_, 11);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_a_1068_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1088_ = v_a_1068_;
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_ematchDiagSource_1086_);
lean_inc(v_sTerms_1084_);
lean_inc(v_mt_1083_);
lean_inc(v_generation_1082_);
lean_inc(v_idx_1081_);
lean_inc(v_size_1076_);
lean_inc(v_proof_x3f_1074_);
lean_inc(v_target_x3f_1073_);
lean_inc(v_congr_1072_);
lean_inc(v_root_1071_);
lean_inc(v_next_1070_);
lean_inc(v_self_1069_);
lean_dec(v_a_1068_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_nat_dec_lt(v_mt_1083_, v___x_1049_);
lean_dec(v_mt_1083_);
if (v___x_1091_ == 0)
{
lean_del_object(v___x_1088_);
lean_dec(v_ematchDiagSource_1086_);
lean_dec(v_sTerms_1084_);
lean_dec(v_generation_1082_);
lean_dec(v_idx_1081_);
lean_dec(v_size_1076_);
lean_dec(v_proof_x3f_1074_);
lean_dec(v_target_x3f_1073_);
lean_dec_ref(v_congr_1072_);
lean_dec_ref(v_root_1071_);
lean_dec_ref(v_next_1070_);
lean_dec_ref(v_self_1069_);
v_as_x27_1050_ = v_tail_1065_;
v_b_1051_ = v___x_1090_;
goto _start;
}
else
{
lean_object* v___x_1094_; 
lean_inc(v___x_1049_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 9, v___x_1049_);
v___x_1094_ = v___x_1088_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_self_1069_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_next_1070_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_root_1071_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_congr_1072_);
lean_ctor_set(v_reuseFailAlloc_1098_, 4, v_target_x3f_1073_);
lean_ctor_set(v_reuseFailAlloc_1098_, 5, v_proof_x3f_1074_);
lean_ctor_set(v_reuseFailAlloc_1098_, 6, v_size_1076_);
lean_ctor_set(v_reuseFailAlloc_1098_, 7, v_idx_1081_);
lean_ctor_set(v_reuseFailAlloc_1098_, 8, v_generation_1082_);
lean_ctor_set(v_reuseFailAlloc_1098_, 9, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1098_, 10, v_sTerms_1084_);
lean_ctor_set(v_reuseFailAlloc_1098_, 11, v_ematchDiagSource_1086_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*12, v_flipped_1075_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*12 + 1, v_interpreted_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*12 + 2, v_ctor_1078_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*12 + 3, v_hasLambdas_1079_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*12 + 4, v_heqProofs_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*12 + 5, v_funCC_1085_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; 
lean_inc(v_head_1064_);
v___x_1095_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1064_, v___x_1094_, v___y_1052_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v___x_1096_; 
lean_dec_ref_known(v___x_1095_, 1);
v___x_1096_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1064_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_dec_ref_known(v___x_1096_, 1);
v_as_x27_1050_ = v_tail_1065_;
v_b_1051_ = v___x_1090_;
goto _start;
}
else
{
lean_dec(v___x_1049_);
return v___x_1096_;
}
}
else
{
lean_dec(v___x_1049_);
return v___x_1095_;
}
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v___x_1049_);
v_a_1100_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1067_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1067_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_st_ref_get(v_a_1109_);
v___x_1121_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1108_, v_a_1109_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_toGoalState_1122_; lean_object* v_ematch_1123_; lean_object* v_a_1124_; lean_object* v_gmt_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_toGoalState_1122_ = lean_ctor_get(v___x_1120_, 0);
lean_inc_ref(v_toGoalState_1122_);
lean_dec(v___x_1120_);
v_ematch_1123_ = lean_ctor_get(v_toGoalState_1122_, 12);
lean_inc_ref(v_ematch_1123_);
lean_dec_ref(v_toGoalState_1122_);
v_a_1124_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1121_, 1);
v_gmt_1125_ = lean_ctor_get(v_ematch_1123_, 1);
lean_inc(v_gmt_1125_);
lean_dec_ref(v_ematch_1123_);
v___x_1126_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1124_);
lean_dec(v_a_1124_);
v___x_1127_ = lean_box(0);
v___x_1128_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1125_, v___x_1126_, v___x_1127_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v___x_1126_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v___x_1128_, 0);
lean_dec(v_unused_1136_);
v___x_1130_ = v___x_1128_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_dec(v___x_1128_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1127_);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1127_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
return v___x_1128_;
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v___x_1120_);
v_a_1137_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1121_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1121_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_root_1145_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1158_, lean_object* v_as_x27_1159_, lean_object* v_b_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1158_, v_as_x27_1159_, v_b_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec(v_as_x27_1159_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1173_, lean_object* v_as_1174_, lean_object* v_as_x27_1175_, lean_object* v_b_1176_, lean_object* v_a_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1173_, v_as_x27_1175_, v_b_1176_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1190_, lean_object* v_as_1191_, lean_object* v_as_x27_1192_, lean_object* v_b_1193_, lean_object* v_a_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1190_, v_as_1191_, v_as_x27_1192_, v_b_1193_, v_a_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec(v_as_x27_1192_);
lean_dec(v_as_1191_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
if (lean_obj_tag(v_a_1207_) == 0)
{
lean_object* v___x_1209_; 
v___x_1209_ = l_List_reverse___redArg(v_a_1208_);
return v___x_1209_;
}
else
{
lean_object* v_head_1210_; lean_object* v_tail_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1220_; 
v_head_1210_ = lean_ctor_get(v_a_1207_, 0);
v_tail_1211_ = lean_ctor_get(v_a_1207_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_a_1207_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1213_ = v_a_1207_;
v_isShared_1214_ = v_isSharedCheck_1220_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_tail_1211_);
lean_inc(v_head_1210_);
lean_dec(v_a_1207_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1220_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = l_Lean_MessageData_ofExpr(v_head_1210_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v_a_1208_);
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_a_1208_);
v___x_1217_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
v_a_1207_ = v_tail_1211_;
v_a_1208_ = v___x_1217_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_fst_1224_, lean_object* v_lams_1225_, lean_object* v_____r_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1221_, v_a_1222_, v___y_1227_);
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
v___y_1239_ = v___y_1227_;
v___y_1240_ = v___y_1228_;
v___y_1241_ = v___y_1229_;
v___y_1242_ = v___y_1230_;
v___y_1243_ = v___y_1231_;
v___y_1244_ = v___y_1232_;
v___y_1245_ = v___y_1233_;
v___y_1246_ = v___y_1234_;
v___y_1247_ = v___y_1235_;
v___y_1248_ = v___y_1236_;
goto v___jp_1238_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_inc(v_fst_1224_);
v___x_1288_ = l_Array_reverse___redArg(v_fst_1224_);
lean_inc(v_snd_1221_);
v___x_1289_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1225_, v_snd_1221_, v___x_1288_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_dec_ref_known(v___x_1289_, 1);
v___y_1239_ = v___y_1227_;
v___y_1240_ = v___y_1228_;
v___y_1241_ = v___y_1229_;
v___y_1242_ = v___y_1230_;
v___y_1243_ = v___y_1231_;
v___y_1244_ = v___y_1232_;
v___y_1245_ = v___y_1233_;
v___y_1246_ = v___y_1234_;
v___y_1247_ = v___y_1235_;
v___y_1248_ = v___y_1236_;
goto v___jp_1238_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_fst_1224_);
lean_dec(v_snd_1221_);
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
lean_dec(v_fst_1224_);
lean_dec(v_snd_1221_);
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
v___jp_1238_:
{
if (lean_obj_tag(v_snd_1221_) == 5)
{
lean_object* v_fn_1249_; lean_object* v_arg_1250_; lean_object* v___x_1251_; 
v_fn_1249_ = lean_ctor_get(v_snd_1221_, 0);
lean_inc_ref(v_fn_1249_);
v_arg_1250_ = lean_ctor_get(v_snd_1221_, 1);
lean_inc_ref(v_arg_1250_);
v___x_1251_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1223_, v___y_1239_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1253_ = lean_box(0);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc(v___y_1239_);
v___x_1254_ = lean_grind_internalize(v_snd_1221_, v_a_1252_, v___x_1253_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
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
v___x_1258_ = lean_array_push(v_fst_1224_, v_arg_1250_);
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
lean_dec(v_fst_1224_);
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
lean_dec_ref_known(v_snd_1221_, 2);
lean_dec_ref(v_fn_1249_);
lean_dec(v_fst_1224_);
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
lean_ctor_set(v___x_1282_, 0, v_fst_1224_);
lean_ctor_set(v___x_1282_, 1, v_snd_1221_);
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
lean_object* v_a_1308_ = _args[2];
lean_object* v_fst_1309_ = _args[3];
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
v_res_1323_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1306_, v_a_1307_, v_a_1308_, v_fst_1309_, v_lams_1310_, v_____r_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
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
lean_dec_ref(v_a_1308_);
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
lean_object* v___y_1351_; lean_object* v_options_1371_; lean_object* v_fst_1372_; lean_object* v_snd_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1410_; 
v_options_1371_ = lean_ctor_get(v___y_1347_, 2);
v_fst_1372_ = lean_ctor_get(v_a_1338_, 0);
v_snd_1373_ = lean_ctor_get(v_a_1338_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_a_1338_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1375_ = v_a_1338_;
v_isShared_1376_ = v_isSharedCheck_1410_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_snd_1373_);
lean_inc(v_fst_1372_);
lean_dec(v_a_1338_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1410_;
goto v_resetjp_1374_;
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
v_resetjp_1374_:
{
lean_object* v_inheritedTraceOptions_1377_; uint8_t v_hasTrace_1378_; 
v_inheritedTraceOptions_1377_ = lean_ctor_get(v___y_1347_, 13);
v_hasTrace_1378_ = lean_ctor_get_uint8(v_options_1371_, sizeof(void*)*1);
if (v_hasTrace_1378_ == 0)
{
lean_del_object(v___x_1375_);
goto v___jp_1379_;
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1382_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1383_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1384_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1377_, v_options_1371_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_del_object(v___x_1375_);
goto v___jp_1379_;
}
else
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_Meta_Grind_updateLastTag(v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_dec_ref_known(v___x_1385_, 1);
v___x_1386_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1373_);
v___x_1387_ = l_Lean_MessageData_ofExpr(v_snd_1373_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 7);
lean_ctor_set(v___x_1375_, 1, v___x_1387_);
lean_ctor_set(v___x_1375_, 0, v___x_1386_);
v___x_1389_ = v___x_1375_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1382_, v___x_1389_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1392_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1392_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1373_, v_a_1336_, v_a_1335_, v_fst_1372_, v_lams_1337_, v_a_1391_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
v___y_1351_ = v___x_1392_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_snd_1373_);
lean_dec(v_fst_1372_);
v_a_1393_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1390_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1390_);
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
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_del_object(v___x_1375_);
lean_dec(v_snd_1373_);
lean_dec(v_fst_1372_);
v_a_1402_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1385_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1385_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
v___jp_1379_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1373_, v_a_1336_, v_a_1335_, v_fst_1372_, v_lams_1337_, v___x_1380_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
v___y_1351_ = v___x_1381_;
goto v___jp_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_lams_1413_, lean_object* v_a_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1411_, v_a_1412_, v_lams_1413_, v_a_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v_lams_1413_);
lean_dec_ref(v_a_1412_);
lean_dec_ref(v_a_1411_);
return v_res_1426_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1431_ = l_Lean_stringToMessageData(v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1432_, lean_object* v_lams_1433_, lean_object* v_as_x27_1434_, lean_object* v_b_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
if (lean_obj_tag(v_as_x27_1434_) == 0)
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_b_1435_);
return v___x_1447_;
}
else
{
lean_object* v_options_1448_; lean_object* v_head_1449_; lean_object* v_tail_1450_; lean_object* v_inheritedTraceOptions_1451_; uint8_t v_hasTrace_1452_; lean_object* v___x_1453_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___x_1477_; uint8_t v_a_1479_; 
v_options_1448_ = lean_ctor_get(v___y_1444_, 2);
v_head_1449_ = lean_ctor_get(v_as_x27_1434_, 0);
v_tail_1450_ = lean_ctor_get(v_as_x27_1434_, 1);
v_inheritedTraceOptions_1451_ = lean_ctor_get(v___y_1444_, 13);
v_hasTrace_1452_ = lean_ctor_get_uint8(v_options_1448_, sizeof(void*)*1);
v___x_1453_ = lean_box(0);
v___x_1477_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
if (v_hasTrace_1452_ == 0)
{
v_a_1479_ = v_hasTrace_1452_;
goto v___jp_1478_;
}
else
{
lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1487_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1451_, v_options_1448_, v___x_1486_);
v_a_1479_ = v___x_1487_;
goto v___jp_1478_;
}
v___jp_1454_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_inc(v_head_1449_);
lean_inc_ref(v___y_1455_);
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___y_1455_);
lean_ctor_set(v___x_1466_, 1, v_head_1449_);
v___x_1467_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1449_, v_a_1432_, v_lams_1433_, v___x_1466_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_dec_ref_known(v___x_1467_, 1);
v_as_x27_1434_ = v_tail_1450_;
v_b_1435_ = v___x_1453_;
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
v___jp_1478_:
{
lean_object* v___x_1480_; 
v___x_1480_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1479_ == 0)
{
v___y_1455_ = v___x_1480_;
v___y_1456_ = v___y_1436_;
v___y_1457_ = v___y_1437_;
v___y_1458_ = v___y_1438_;
v___y_1459_ = v___y_1439_;
v___y_1460_ = v___y_1440_;
v___y_1461_ = v___y_1441_;
v___y_1462_ = v___y_1442_;
v___y_1463_ = v___y_1443_;
v___y_1464_ = v___y_1444_;
v___y_1465_ = v___y_1445_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_Meta_Grind_updateLastTag(v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec_ref_known(v___x_1481_, 1);
v___x_1482_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1449_);
v___x_1483_ = l_Lean_MessageData_ofExpr(v_head_1449_);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1477_, v___x_1484_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec_ref_known(v___x_1485_, 1);
v___y_1455_ = v___x_1480_;
v___y_1456_ = v___y_1436_;
v___y_1457_ = v___y_1437_;
v___y_1458_ = v___y_1438_;
v___y_1459_ = v___y_1439_;
v___y_1460_ = v___y_1440_;
v___y_1461_ = v___y_1441_;
v___y_1462_ = v___y_1442_;
v___y_1463_ = v___y_1443_;
v___y_1464_ = v___y_1444_;
v___y_1465_ = v___y_1445_;
goto v___jp_1454_;
}
else
{
return v___x_1485_;
}
}
else
{
return v___x_1481_;
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
lean_object* v_options_1521_; lean_object* v_head_1522_; lean_object* v_tail_1523_; lean_object* v_inheritedTraceOptions_1524_; uint8_t v_hasTrace_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; uint8_t v_a_1552_; 
v_options_1521_ = lean_ctor_get(v___y_1517_, 2);
v_head_1522_ = lean_ctor_get(v_as_x27_1507_, 0);
v_tail_1523_ = lean_ctor_get(v_as_x27_1507_, 1);
v_inheritedTraceOptions_1524_ = lean_ctor_get(v___y_1517_, 13);
v_hasTrace_1525_ = lean_ctor_get_uint8(v_options_1521_, sizeof(void*)*1);
v___x_1526_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1527_ = lean_box(0);
if (v_hasTrace_1525_ == 0)
{
v_a_1552_ = v_hasTrace_1525_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_1559_; uint8_t v___x_1560_; 
v___x_1559_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1560_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1524_, v_options_1521_, v___x_1559_);
v_a_1552_ = v___x_1560_;
goto v___jp_1551_;
}
v___jp_1528_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_inc(v_head_1522_);
lean_inc_ref(v___y_1529_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___y_1529_);
lean_ctor_set(v___x_1540_, 1, v_head_1522_);
v___x_1541_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1522_, v_a_1504_, v_lams_1505_, v___x_1540_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1542_; 
lean_dec_ref_known(v___x_1541_, 1);
v___x_1542_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1504_, v_lams_1505_, v_tail_1523_, v___x_1527_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
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
v___jp_1551_:
{
lean_object* v___x_1553_; 
v___x_1553_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1552_ == 0)
{
v___y_1529_ = v___x_1553_;
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
goto v___jp_1528_;
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
lean_inc(v_head_1522_);
v___x_1556_ = l_Lean_MessageData_ofExpr(v_head_1522_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1526_, v___x_1557_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_dec_ref_known(v___x_1558_, 1);
v___y_1529_ = v___x_1553_;
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
goto v___jp_1528_;
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1561_, lean_object* v_lams_1562_, lean_object* v_as_1563_, lean_object* v_as_x27_1564_, lean_object* v_b_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1561_, v_lams_1562_, v_as_1563_, v_as_x27_1564_, v_b_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec(v_as_x27_1564_);
lean_dec(v_as_1563_);
lean_dec_ref(v_lams_1562_);
lean_dec_ref(v_a_1561_);
return v_res_1577_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1584_, lean_object* v_lams_1585_, lean_object* v_as_1586_, size_t v_sz_1587_, size_t v_i_1588_, lean_object* v_b_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_usize_dec_lt(v_i_1588_, v_sz_1587_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_b_1589_);
return v___x_1602_;
}
else
{
lean_object* v_options_1603_; lean_object* v_inheritedTraceOptions_1604_; uint8_t v_hasTrace_1605_; lean_object* v___x_1606_; lean_object* v_a_1607_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; 
v_options_1603_ = lean_ctor_get(v___y_1598_, 2);
v_inheritedTraceOptions_1604_ = lean_ctor_get(v___y_1598_, 13);
v_hasTrace_1605_ = lean_ctor_get_uint8(v_options_1603_, sizeof(void*)*1);
v___x_1606_ = lean_box(0);
v_a_1607_ = lean_array_uget_borrowed(v_as_1586_, v_i_1588_);
if (v_hasTrace_1605_ == 0)
{
v___y_1609_ = v___y_1590_;
v___y_1610_ = v___y_1591_;
v___y_1611_ = v___y_1592_;
v___y_1612_ = v___y_1593_;
v___y_1613_ = v___y_1594_;
v___y_1614_ = v___y_1595_;
v___y_1615_ = v___y_1596_;
v___y_1616_ = v___y_1597_;
v___y_1617_ = v___y_1598_;
v___y_1618_ = v___y_1599_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1635_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1636_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1604_, v_options_1603_, v___x_1635_);
if (v___x_1636_ == 0)
{
v___y_1609_ = v___y_1590_;
v___y_1610_ = v___y_1591_;
v___y_1611_ = v___y_1592_;
v___y_1612_ = v___y_1593_;
v___y_1613_ = v___y_1594_;
v___y_1614_ = v___y_1595_;
v___y_1615_ = v___y_1596_;
v___y_1616_ = v___y_1597_;
v___y_1617_ = v___y_1598_;
v___y_1618_ = v___y_1599_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Meta_Grind_updateLastTag(v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v___x_1638_; 
lean_dec_ref_known(v___x_1637_, 1);
v___x_1638_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1607_, v___y_1590_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1607_);
v___x_1641_ = l_Lean_MessageData_ofExpr(v_a_1607_);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1639_);
lean_dec(v_a_1639_);
v___x_1646_ = lean_box(0);
v___x_1647_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1645_, v___x_1646_);
v___x_1648_ = l_Lean_MessageData_ofList(v___x_1647_);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1644_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1634_, v___x_1649_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_dec_ref_known(v___x_1650_, 1);
v___y_1609_ = v___y_1590_;
v___y_1610_ = v___y_1591_;
v___y_1611_ = v___y_1592_;
v___y_1612_ = v___y_1593_;
v___y_1613_ = v___y_1594_;
v___y_1614_ = v___y_1595_;
v___y_1615_ = v___y_1596_;
v___y_1616_ = v___y_1597_;
v___y_1617_ = v___y_1598_;
v___y_1618_ = v___y_1599_;
goto v___jp_1608_;
}
else
{
return v___x_1650_;
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1638_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1638_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
return v___x_1637_;
}
}
}
v___jp_1608_:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1607_, v___y_1609_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1620_);
lean_dec(v_a_1620_);
v___x_1622_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1584_, v_lams_1585_, v___x_1621_, v___x_1621_, v___x_1606_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___x_1621_);
if (lean_obj_tag(v___x_1622_) == 0)
{
size_t v___x_1623_; size_t v___x_1624_; 
lean_dec_ref_known(v___x_1622_, 1);
v___x_1623_ = ((size_t)1ULL);
v___x_1624_ = lean_usize_add(v_i_1588_, v___x_1623_);
v_i_1588_ = v___x_1624_;
v_b_1589_ = v___x_1606_;
goto _start;
}
else
{
return v___x_1622_;
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_a_1626_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1619_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1619_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1659_ = _args[0];
lean_object* v_lams_1660_ = _args[1];
lean_object* v_as_1661_ = _args[2];
lean_object* v_sz_1662_ = _args[3];
lean_object* v_i_1663_ = _args[4];
lean_object* v_b_1664_ = _args[5];
lean_object* v___y_1665_ = _args[6];
lean_object* v___y_1666_ = _args[7];
lean_object* v___y_1667_ = _args[8];
lean_object* v___y_1668_ = _args[9];
lean_object* v___y_1669_ = _args[10];
lean_object* v___y_1670_ = _args[11];
lean_object* v___y_1671_ = _args[12];
lean_object* v___y_1672_ = _args[13];
lean_object* v___y_1673_ = _args[14];
lean_object* v___y_1674_ = _args[15];
lean_object* v___y_1675_ = _args[16];
_start:
{
size_t v_sz_boxed_1676_; size_t v_i_boxed_1677_; lean_object* v_res_1678_; 
v_sz_boxed_1676_ = lean_unbox_usize(v_sz_1662_);
lean_dec(v_sz_1662_);
v_i_boxed_1677_ = lean_unbox_usize(v_i_1663_);
lean_dec(v_i_1663_);
v_res_1678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1659_, v_lams_1660_, v_as_1661_, v_sz_boxed_1676_, v_i_boxed_1677_, v_b_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v_as_1661_);
lean_dec_ref(v_lams_1660_);
lean_dec_ref(v_a_1659_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1679_, lean_object* v_lams_1680_, lean_object* v_as_1681_, size_t v_sz_1682_, size_t v_i_1683_, lean_object* v_b_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
uint8_t v___x_1696_; 
v___x_1696_ = lean_usize_dec_lt(v_i_1683_, v_sz_1682_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v_b_1684_);
return v___x_1697_;
}
else
{
lean_object* v_options_1698_; lean_object* v_inheritedTraceOptions_1699_; uint8_t v_hasTrace_1700_; lean_object* v___x_1701_; lean_object* v_a_1702_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; 
v_options_1698_ = lean_ctor_get(v___y_1693_, 2);
v_inheritedTraceOptions_1699_ = lean_ctor_get(v___y_1693_, 13);
v_hasTrace_1700_ = lean_ctor_get_uint8(v_options_1698_, sizeof(void*)*1);
v___x_1701_ = lean_box(0);
v_a_1702_ = lean_array_uget_borrowed(v_as_1681_, v_i_1683_);
if (v_hasTrace_1700_ == 0)
{
v___y_1704_ = v___y_1685_;
v___y_1705_ = v___y_1686_;
v___y_1706_ = v___y_1687_;
v___y_1707_ = v___y_1688_;
v___y_1708_ = v___y_1689_;
v___y_1709_ = v___y_1690_;
v___y_1710_ = v___y_1691_;
v___y_1711_ = v___y_1692_;
v___y_1712_ = v___y_1693_;
v___y_1713_ = v___y_1694_;
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
v___y_1704_ = v___y_1685_;
v___y_1705_ = v___y_1686_;
v___y_1706_ = v___y_1687_;
v___y_1707_ = v___y_1688_;
v___y_1708_ = v___y_1689_;
v___y_1709_ = v___y_1690_;
v___y_1710_ = v___y_1691_;
v___y_1711_ = v___y_1692_;
v___y_1712_ = v___y_1693_;
v___y_1713_ = v___y_1694_;
goto v___jp_1703_;
}
else
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Meta_Grind_updateLastTag(v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; 
lean_dec_ref_known(v___x_1732_, 1);
v___x_1733_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1702_, v___y_1685_);
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
v___x_1745_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1729_, v___x_1744_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_dec_ref_known(v___x_1745_, 1);
v___y_1704_ = v___y_1685_;
v___y_1705_ = v___y_1686_;
v___y_1706_ = v___y_1687_;
v___y_1707_ = v___y_1688_;
v___y_1708_ = v___y_1689_;
v___y_1709_ = v___y_1690_;
v___y_1710_ = v___y_1691_;
v___y_1711_ = v___y_1692_;
v___y_1712_ = v___y_1693_;
v___y_1713_ = v___y_1694_;
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
v___x_1717_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1679_, v_lams_1680_, v___x_1716_, v___x_1716_, v___x_1701_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___x_1716_);
if (lean_obj_tag(v___x_1717_) == 0)
{
size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
lean_dec_ref_known(v___x_1717_, 1);
v___x_1718_ = ((size_t)1ULL);
v___x_1719_ = lean_usize_add(v_i_1683_, v___x_1718_);
v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1679_, v_lams_1680_, v_as_1681_, v_sz_1682_, v___x_1719_, v___x_1701_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
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
v___x_1796_ = lean_st_ref_get(v_a_1782_);
v___x_1797_ = l_Lean_instInhabitedExpr;
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_nat_sub(v___x_1793_, v___x_1798_);
v___x_1800_ = lean_array_get_borrowed(v___x_1797_, v_lams_1780_, v___x_1799_);
lean_dec(v___x_1799_);
lean_inc(v___x_1800_);
v___x_1801_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1796_, v___x_1800_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec(v___x_1796_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v_options_1826_; uint8_t v_hasTrace_1827_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v_options_1826_ = lean_ctor_get(v_a_1790_, 2);
v_hasTrace_1827_ = lean_ctor_get_uint8(v_options_1826_, sizeof(void*)*1);
if (v_hasTrace_1827_ == 0)
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
lean_object* v_inheritedTraceOptions_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v_inheritedTraceOptions_1828_ = lean_ctor_get(v_a_1790_, 13);
v___x_1829_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1830_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1831_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1828_, v_options_1826_, v___x_1830_);
if (v___x_1831_ == 0)
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
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Meta_Grind_updateLastTag(v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec_ref_known(v___x_1832_, 1);
v___x_1833_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1781_);
v___x_1834_ = lean_array_to_list(v_fns_1781_);
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
lean_inc_ref(v_lams_1780_);
v___x_1841_ = lean_array_to_list(v_lams_1780_);
v___x_1842_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1841_, v___x_1835_);
v___x_1843_ = l_Lean_MessageData_ofList(v___x_1842_);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1840_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1829_, v___x_1844_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_dec_ref_known(v___x_1845_, 1);
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
return v___x_1845_;
}
}
else
{
lean_dec(v_a_1802_);
lean_dec_ref(v_fns_1781_);
lean_dec_ref(v_lams_1780_);
return v___x_1832_;
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
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec_ref(v_fns_1781_);
lean_dec_ref(v_lams_1780_);
v_a_1846_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1801_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1801_);
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
lean_dec_ref(v_fns_1781_);
lean_dec_ref(v_lams_1780_);
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
lean_object* v_binderType_1993_; uint8_t v___x_1994_; 
v_binderType_1993_ = lean_ctor_get(v_a_1992_, 1);
v___x_1994_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_d_1979_, v_binderType_1993_);
if (v___x_1994_ == 0)
{
v_a_1985_ = v___x_1991_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_inc_ref(v_a_1992_);
v___x_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1995_, 0, v_a_1992_);
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v___x_1990_);
return v___x_1997_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2028_, lean_object* v_lams_u2081_2029_, lean_object* v_as_2030_, size_t v_sz_2031_, size_t v_i_2032_, lean_object* v_b_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_a_2046_; uint8_t v___x_2050_; 
v___x_2050_ = lean_usize_dec_lt(v_i_2032_, v_sz_2031_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_b_2033_);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; lean_object* v_a_2053_; 
v___x_2052_ = lean_box(0);
v_a_2053_ = lean_array_uget_borrowed(v_as_2030_, v_i_2032_);
if (lean_obj_tag(v_a_2053_) == 6)
{
lean_object* v_binderType_2054_; lean_object* v_body_2055_; lean_object* v___x_2056_; 
v_binderType_2054_ = lean_ctor_get(v_a_2053_, 1);
v_body_2055_ = lean_ctor_get(v_a_2053_, 2);
lean_inc_ref(v_binderType_2054_);
v___x_2056_ = l_Lean_Meta_getLevel(v_binderType_2054_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2059_ = lean_box(0);
v___x_2060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2060_, 0, v_a_2057_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
lean_inc_ref(v___x_2060_);
v___x_2061_ = l_Lean_mkConst(v___x_2058_, v___x_2060_);
lean_inc_ref(v_binderType_2054_);
v___x_2062_ = l_Lean_Expr_app___override(v___x_2061_, v_binderType_2054_);
v___x_2063_ = lean_box(0);
v___x_2064_ = l_Lean_Meta_synthInstance_x3f(v___x_2062_, v___x_2063_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
if (lean_obj_tag(v_a_2065_) == 1)
{
lean_object* v_val_2066_; lean_object* v___x_2067_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; uint8_t v___x_2132_; 
v_val_2066_ = lean_ctor_get(v_a_2065_, 0);
lean_inc(v_val_2066_);
lean_dec_ref_known(v_a_2065_, 1);
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2132_ = l_Lean_Expr_hasLooseBVars(v_body_2055_);
if (v___x_2132_ == 0)
{
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2060_);
v___x_2134_ = l_Lean_mkConst(v___x_2133_, v___x_2060_);
lean_inc_ref(v_binderType_2054_);
v___x_2135_ = l_Lean_Expr_app___override(v___x_2134_, v_binderType_2054_);
v___x_2136_ = l_Lean_Meta_synthInstance_x3f(v___x_2135_, v___x_2063_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
if (lean_obj_tag(v_a_2137_) == 0)
{
lean_dec(v_val_2066_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2046_ = v___x_2052_;
goto v___jp_2045_;
}
else
{
lean_dec_ref_known(v_a_2137_, 1);
if (v___x_2132_ == 0)
{
lean_dec(v_val_2066_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2046_ = v___x_2052_;
goto v___jp_2045_;
}
else
{
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
goto v___jp_2068_;
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec(v_val_2066_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2138_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2136_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2136_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
v___jp_2068_:
{
lean_object* v___x_2079_; 
v___x_2079_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2028_, v_binderType_2054_);
if (lean_obj_tag(v___x_2079_) == 1)
{
lean_object* v_val_2080_; 
v_val_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_val_2080_);
lean_dec_ref_known(v___x_2079_, 1);
if (lean_obj_tag(v_val_2080_) == 6)
{
lean_object* v_binderType_2081_; lean_object* v_body_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_binderType_2081_ = lean_ctor_get(v_val_2080_, 1);
lean_inc_ref(v_binderType_2081_);
v_body_2082_ = lean_ctor_get(v_val_2080_, 2);
lean_inc_ref(v_body_2082_);
lean_dec_ref_known(v_val_2080_, 3);
v___x_2083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2084_ = l_Lean_mkConst(v___x_2083_, v___x_2060_);
v___x_2085_ = l_Lean_mkAppB(v___x_2084_, v_binderType_2081_, v_val_2066_);
v___x_2086_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2085_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = lean_array_fget_borrowed(v_lams_u2081_2029_, v___x_2067_);
v___x_2089_ = lean_array_fget_borrowed(v_lams_u2082_2028_, v___x_2067_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
lean_inc(v___y_2076_);
lean_inc_ref(v___y_2075_);
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc(v___y_2069_);
lean_inc(v___x_2089_);
lean_inc(v___x_2088_);
v___x_2090_ = lean_grind_mk_eq_proof(v___x_2088_, v___x_2089_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = lean_expr_instantiate1(v_body_2055_, v_a_2087_);
v___x_2093_ = lean_expr_instantiate1(v_body_2082_, v_a_2087_);
lean_dec_ref(v_body_2082_);
v___x_2094_ = l_Lean_Meta_mkCongrFun(v_a_2091_, v_a_2087_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = l_Lean_Meta_mkEq(v___x_2092_, v___x_2093_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = l_Lean_Meta_mkExpectedPropHint(v_a_2095_, v_a_2097_);
v___x_2099_ = l_Lean_Meta_Grind_pushNewFact(v___x_2098_, v___x_2067_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_dec_ref_known(v___x_2099_, 1);
v_a_2046_ = v___x_2052_;
goto v___jp_2045_;
}
else
{
return v___x_2099_;
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_a_2095_);
v_a_2100_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2096_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2096_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v___x_2093_);
lean_dec_ref(v___x_2092_);
v_a_2108_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2094_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2094_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v_a_2087_);
lean_dec_ref(v_body_2082_);
v_a_2116_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2090_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2090_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v_body_2082_);
v_a_2124_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2086_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2086_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_dec(v_val_2080_);
lean_dec(v_val_2066_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2046_ = v___x_2052_;
goto v___jp_2045_;
}
}
else
{
lean_dec(v___x_2079_);
lean_dec(v_val_2066_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2046_ = v___x_2052_;
goto v___jp_2045_;
}
}
}
else
{
lean_dec(v_a_2065_);
lean_dec_ref_known(v___x_2060_, 2);
v_a_2046_ = v___x_2052_;
goto v___jp_2045_;
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref_known(v___x_2060_, 2);
v_a_2146_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2064_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2064_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
v_a_2154_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2056_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2056_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
v_a_2046_ = v___x_2052_;
goto v___jp_2045_;
}
}
v___jp_2045_:
{
size_t v___x_2047_; size_t v___x_2048_; 
v___x_2047_ = ((size_t)1ULL);
v___x_2048_ = lean_usize_add(v_i_2032_, v___x_2047_);
v_i_2032_ = v___x_2048_;
v_b_2033_ = v_a_2046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2162_ = _args[0];
lean_object* v_lams_u2081_2163_ = _args[1];
lean_object* v_as_2164_ = _args[2];
lean_object* v_sz_2165_ = _args[3];
lean_object* v_i_2166_ = _args[4];
lean_object* v_b_2167_ = _args[5];
lean_object* v___y_2168_ = _args[6];
lean_object* v___y_2169_ = _args[7];
lean_object* v___y_2170_ = _args[8];
lean_object* v___y_2171_ = _args[9];
lean_object* v___y_2172_ = _args[10];
lean_object* v___y_2173_ = _args[11];
lean_object* v___y_2174_ = _args[12];
lean_object* v___y_2175_ = _args[13];
lean_object* v___y_2176_ = _args[14];
lean_object* v___y_2177_ = _args[15];
lean_object* v___y_2178_ = _args[16];
_start:
{
size_t v_sz_boxed_2179_; size_t v_i_boxed_2180_; lean_object* v_res_2181_; 
v_sz_boxed_2179_ = lean_unbox_usize(v_sz_2165_);
lean_dec(v_sz_2165_);
v_i_boxed_2180_ = lean_unbox_usize(v_i_2166_);
lean_dec(v_i_2166_);
v_res_2181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2162_, v_lams_u2081_2163_, v_as_2164_, v_sz_boxed_2179_, v_i_boxed_2180_, v_b_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v_as_2164_);
lean_dec_ref(v_lams_u2081_2163_);
lean_dec_ref(v_lams_u2082_2162_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2182_, lean_object* v_lams_u2082_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2195_ = lean_array_get_size(v_lams_u2081_2182_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_nat_dec_eq(v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = lean_array_get_size(v_lams_u2082_2183_);
v___x_2199_ = lean_nat_dec_eq(v___x_2198_, v___x_2196_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; size_t v_sz_2201_; size_t v___x_2202_; lean_object* v___x_2203_; 
v___x_2200_ = lean_box(0);
v_sz_2201_ = lean_array_size(v_lams_u2081_2182_);
v___x_2202_ = ((size_t)0ULL);
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2183_, v_lams_u2081_2182_, v_lams_u2081_2182_, v_sz_2201_, v___x_2202_, v___x_2200_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v___x_2203_, 0);
lean_dec(v_unused_2211_);
v___x_2205_ = v___x_2203_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v___x_2203_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2200_);
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2200_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
return v___x_2203_;
}
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_box(0);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2216_, lean_object* v_lams_u2082_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2216_, v_lams_u2082_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_lams_u2082_2217_);
lean_dec_ref(v_lams_u2081_2216_);
return v_res_2229_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2230_){
_start:
{
uint8_t v___x_2231_; 
v___x_2231_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2232_){
_start:
{
uint8_t v_res_2233_; lean_object* v_r_2234_; 
v_res_2233_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2232_);
lean_dec_ref(v_x_2232_);
v_r_2234_ = lean_box(v_res_2233_);
return v_r_2234_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2235_, lean_object* v_x_2236_){
_start:
{
uint8_t v___x_2237_; 
v___x_2237_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2238_, lean_object* v_x_2239_){
_start:
{
uint8_t v_res_2240_; lean_object* v_r_2241_; 
v_res_2240_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2238_, v_x_2239_);
lean_dec_ref(v_x_2239_);
v_r_2241_ = lean_box(v_res_2240_);
return v_r_2241_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2242_, lean_object* v_v_2243_, lean_object* v_i_2244_){
_start:
{
lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2245_ = lean_array_get_size(v_xs_2242_);
v___x_2246_ = lean_nat_dec_lt(v_i_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; 
lean_dec(v_i_2244_);
v___x_2247_ = lean_box(0);
return v___x_2247_;
}
else
{
lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2248_ = lean_array_fget_borrowed(v_xs_2242_, v_i_2244_);
v___x_2249_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_2248_, v_v_2243_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_unsigned_to_nat(1u);
v___x_2251_ = lean_nat_add(v_i_2244_, v___x_2250_);
lean_dec(v_i_2244_);
v_i_2244_ = v___x_2251_;
goto _start;
}
else
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_i_2244_);
return v___x_2253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2254_, lean_object* v_v_2255_, lean_object* v_i_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2254_, v_v_2255_, v_i_2256_);
lean_dec_ref(v_v_2255_);
lean_dec_ref(v_xs_2254_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2258_, lean_object* v_v_2259_){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_unsigned_to_nat(0u);
v___x_2261_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2258_, v_v_2259_, v___x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2262_, lean_object* v_v_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2262_, v_v_2263_);
lean_dec_ref(v_v_2263_);
lean_dec_ref(v_xs_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2265_, size_t v_x_2266_, lean_object* v_x_2267_){
_start:
{
if (lean_obj_tag(v_x_2265_) == 0)
{
lean_object* v_es_2268_; lean_object* v___x_2269_; size_t v___x_2270_; size_t v___x_2271_; lean_object* v_j_2272_; lean_object* v_entry_2273_; 
v_es_2268_ = lean_ctor_get(v_x_2265_, 0);
v___x_2269_ = lean_box(2);
v___x_2270_ = ((size_t)31ULL);
v___x_2271_ = lean_usize_land(v_x_2266_, v___x_2270_);
v_j_2272_ = lean_usize_to_nat(v___x_2271_);
v_entry_2273_ = lean_array_get(v___x_2269_, v_es_2268_, v_j_2272_);
switch(lean_obj_tag(v_entry_2273_))
{
case 0:
{
lean_object* v_key_2274_; uint8_t v___x_2275_; 
v_key_2274_ = lean_ctor_get(v_entry_2273_, 0);
lean_inc(v_key_2274_);
lean_dec_ref_known(v_entry_2273_, 2);
v___x_2275_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2267_, v_key_2274_);
lean_dec(v_key_2274_);
if (v___x_2275_ == 0)
{
lean_dec(v_j_2272_);
return v_x_2265_;
}
else
{
lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2283_; 
lean_inc_ref(v_es_2268_);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2283_ == 0)
{
lean_object* v_unused_2284_; 
v_unused_2284_ = lean_ctor_get(v_x_2265_, 0);
lean_dec(v_unused_2284_);
v___x_2277_ = v_x_2265_;
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
else
{
lean_dec(v_x_2265_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2279_ = lean_array_set(v_es_2268_, v_j_2272_, v___x_2269_);
lean_dec(v_j_2272_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2279_);
v___x_2281_ = v___x_2277_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
case 1:
{
lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2319_; 
lean_inc_ref(v_es_2268_);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_x_2265_, 0);
lean_dec(v_unused_2320_);
v___x_2286_ = v_x_2265_;
v_isShared_2287_ = v_isSharedCheck_2319_;
goto v_resetjp_2285_;
}
else
{
lean_dec(v_x_2265_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2319_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_node_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2318_; 
v_node_2288_ = lean_ctor_get(v_entry_2273_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_entry_2273_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2290_ = v_entry_2273_;
v_isShared_2291_ = v_isSharedCheck_2318_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_node_2288_);
lean_dec(v_entry_2273_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2318_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
size_t v___x_2292_; lean_object* v_entries_2293_; size_t v___x_2294_; lean_object* v_newNode_2295_; lean_object* v___x_2296_; 
v___x_2292_ = ((size_t)5ULL);
v_entries_2293_ = lean_array_set(v_es_2268_, v_j_2272_, v___x_2269_);
v___x_2294_ = lean_usize_shift_right(v_x_2266_, v___x_2292_);
v_newNode_2295_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2288_, v___x_2294_, v_x_2267_);
lean_inc_ref(v_newNode_2295_);
v___x_2296_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2295_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v___x_2298_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v_newNode_2295_);
v___x_2298_ = v___x_2290_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_newNode_2295_);
v___x_2298_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2299_ = lean_array_set(v_entries_2293_, v_j_2272_, v___x_2298_);
lean_dec(v_j_2272_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2299_);
v___x_2301_ = v___x_2286_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
else
{
lean_object* v_val_2304_; lean_object* v_fst_2305_; lean_object* v_snd_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_newNode_2295_);
lean_del_object(v___x_2290_);
v_val_2304_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_val_2304_);
lean_dec_ref_known(v___x_2296_, 1);
v_fst_2305_ = lean_ctor_get(v_val_2304_, 0);
v_snd_2306_ = lean_ctor_get(v_val_2304_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_val_2304_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2308_ = v_val_2304_;
v_isShared_2309_ = v_isSharedCheck_2317_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_snd_2306_);
lean_inc(v_fst_2305_);
lean_dec(v_val_2304_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2317_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_fst_2305_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_snd_2306_);
v___x_2311_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2312_ = lean_array_set(v_entries_2293_, v_j_2272_, v___x_2311_);
lean_dec(v_j_2272_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2312_);
v___x_2314_ = v___x_2286_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2272_);
return v_x_2265_;
}
}
}
else
{
lean_object* v_ks_2321_; lean_object* v_vs_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2336_; 
v_ks_2321_ = lean_ctor_get(v_x_2265_, 0);
v_vs_2322_ = lean_ctor_get(v_x_2265_, 1);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_x_2265_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2324_ = v_x_2265_;
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_vs_2322_);
lean_inc(v_ks_2321_);
lean_dec(v_x_2265_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2321_, v_x_2267_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v___x_2328_; 
if (v_isShared_2325_ == 0)
{
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_ks_2321_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_vs_2322_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
else
{
lean_object* v_val_2330_; lean_object* v_keys_x27_2331_; lean_object* v_vals_x27_2332_; lean_object* v___x_2334_; 
v_val_2330_ = lean_ctor_get(v___x_2326_, 0);
lean_inc_n(v_val_2330_, 2);
lean_dec_ref_known(v___x_2326_, 1);
v_keys_x27_2331_ = l_Array_eraseIdx___redArg(v_ks_2321_, v_val_2330_);
v_vals_x27_2332_ = l_Array_eraseIdx___redArg(v_vs_2322_, v_val_2330_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 1, v_vals_x27_2332_);
lean_ctor_set(v___x_2324_, 0, v_keys_x27_2331_);
v___x_2334_ = v___x_2324_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_keys_x27_2331_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_vals_x27_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
size_t v_x_21933__boxed_2340_; lean_object* v_res_2341_; 
v_x_21933__boxed_2340_ = lean_unbox_usize(v_x_2338_);
lean_dec(v_x_2338_);
v_res_2341_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2337_, v_x_21933__boxed_2340_, v_x_2339_);
lean_dec_ref(v_x_2339_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
uint64_t v___x_2344_; size_t v_h_2345_; lean_object* v___x_2346_; 
v___x_2344_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2343_);
v_h_2345_ = lean_uint64_to_usize(v___x_2344_);
v___x_2346_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2342_, v_h_2345_, v_x_2343_);
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
lean_object* v_k_x27_2388_; uint8_t v___x_2389_; 
v_k_x27_2388_ = lean_array_fget_borrowed(v_keys_2381_, v_i_2383_);
v___x_2389_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_2384_, v_k_x27_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_unsigned_to_nat(1u);
v___x_2391_ = lean_nat_add(v_i_2383_, v___x_2390_);
lean_dec(v_i_2383_);
v_i_2383_ = v___x_2391_;
goto _start;
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_array_fget_borrowed(v_vals_2382_, v_i_2383_);
lean_dec(v_i_2383_);
lean_inc(v___x_2393_);
v___x_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2395_, lean_object* v_vals_2396_, lean_object* v_i_2397_, lean_object* v_k_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2395_, v_vals_2396_, v_i_2397_, v_k_2398_);
lean_dec_ref(v_k_2398_);
lean_dec_ref(v_vals_2396_);
lean_dec_ref(v_keys_2395_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2400_, size_t v_x_2401_, lean_object* v_x_2402_){
_start:
{
if (lean_obj_tag(v_x_2400_) == 0)
{
lean_object* v_es_2403_; lean_object* v___x_2404_; size_t v___x_2405_; size_t v___x_2406_; lean_object* v_j_2407_; lean_object* v___x_2408_; 
v_es_2403_ = lean_ctor_get(v_x_2400_, 0);
v___x_2404_ = lean_box(2);
v___x_2405_ = ((size_t)31ULL);
v___x_2406_ = lean_usize_land(v_x_2401_, v___x_2405_);
v_j_2407_ = lean_usize_to_nat(v___x_2406_);
v___x_2408_ = lean_array_get_borrowed(v___x_2404_, v_es_2403_, v_j_2407_);
lean_dec(v_j_2407_);
switch(lean_obj_tag(v___x_2408_))
{
case 0:
{
lean_object* v_key_2409_; lean_object* v_val_2410_; uint8_t v___x_2411_; 
v_key_2409_ = lean_ctor_get(v___x_2408_, 0);
v_val_2410_ = lean_ctor_get(v___x_2408_, 1);
v___x_2411_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2402_, v_key_2409_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_box(0);
return v___x_2412_;
}
else
{
lean_object* v___x_2413_; 
lean_inc(v_val_2410_);
v___x_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_val_2410_);
return v___x_2413_;
}
}
case 1:
{
lean_object* v_node_2414_; size_t v___x_2415_; size_t v___x_2416_; 
v_node_2414_ = lean_ctor_get(v___x_2408_, 0);
v___x_2415_ = ((size_t)5ULL);
v___x_2416_ = lean_usize_shift_right(v_x_2401_, v___x_2415_);
v_x_2400_ = v_node_2414_;
v_x_2401_ = v___x_2416_;
goto _start;
}
default: 
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_box(0);
return v___x_2418_;
}
}
}
else
{
lean_object* v_ks_2419_; lean_object* v_vs_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v_ks_2419_ = lean_ctor_get(v_x_2400_, 0);
v_vs_2420_ = lean_ctor_get(v_x_2400_, 1);
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2419_, v_vs_2420_, v___x_2421_, v_x_2402_);
return v___x_2422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2423_, lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
size_t v_x_22144__boxed_2426_; lean_object* v_res_2427_; 
v_x_22144__boxed_2426_ = lean_unbox_usize(v_x_2424_);
lean_dec(v_x_2424_);
v_res_2427_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2423_, v_x_22144__boxed_2426_, v_x_2425_);
lean_dec_ref(v_x_2425_);
lean_dec_ref(v_x_2423_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2428_, lean_object* v_x_2429_){
_start:
{
uint64_t v___x_2430_; size_t v___x_2431_; lean_object* v___x_2432_; 
v___x_2430_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2429_);
v___x_2431_ = lean_uint64_to_usize(v___x_2430_);
v___x_2432_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2428_, v___x_2431_, v_x_2429_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2433_, lean_object* v_x_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2433_, v_x_2434_);
lean_dec_ref(v_x_2434_);
lean_dec_ref(v_x_2433_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2436_, lean_object* v_b_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
if (lean_obj_tag(v_as_x27_2436_) == 0)
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v_b_2437_);
return v___x_2449_;
}
else
{
lean_object* v_head_2450_; lean_object* v_tail_2451_; lean_object* v___x_2452_; lean_object* v_toGoalState_2453_; lean_object* v_ematch_2454_; lean_object* v_delayedThmInsts_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_head_2450_ = lean_ctor_get(v_as_x27_2436_, 0);
v_tail_2451_ = lean_ctor_get(v_as_x27_2436_, 1);
v___x_2452_ = lean_st_ref_get(v___y_2438_);
v_toGoalState_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc_ref(v_toGoalState_2453_);
lean_dec(v___x_2452_);
v_ematch_2454_ = lean_ctor_get(v_toGoalState_2453_, 12);
lean_inc_ref(v_ematch_2454_);
lean_dec_ref(v_toGoalState_2453_);
v_delayedThmInsts_2455_ = lean_ctor_get(v_ematch_2454_, 10);
lean_inc_ref(v_delayedThmInsts_2455_);
lean_dec_ref(v_ematch_2454_);
v___x_2456_ = lean_box(0);
v___x_2457_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2455_, v_head_2450_);
lean_dec_ref(v_delayedThmInsts_2455_);
if (lean_obj_tag(v___x_2457_) == 1)
{
lean_object* v_val_2458_; lean_object* v___x_2459_; lean_object* v_toGoalState_2460_; lean_object* v_ematch_2461_; lean_object* v_mvarId_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2516_; 
v_val_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_val_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = lean_st_ref_take(v___y_2438_);
v_toGoalState_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc_ref(v_toGoalState_2460_);
v_ematch_2461_ = lean_ctor_get(v_toGoalState_2460_, 12);
lean_inc_ref(v_ematch_2461_);
v_mvarId_2462_ = lean_ctor_get(v___x_2459_, 1);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v___x_2459_, 0);
lean_dec(v_unused_2517_);
v___x_2464_ = v___x_2459_;
v_isShared_2465_ = v_isSharedCheck_2516_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_mvarId_2462_);
lean_dec(v___x_2459_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2516_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_nextDeclIdx_2466_; lean_object* v_enodeMap_2467_; lean_object* v_exprs_2468_; lean_object* v_parents_2469_; lean_object* v_congrTable_2470_; lean_object* v_appMap_2471_; lean_object* v_indicesFound_2472_; lean_object* v_newFacts_2473_; uint8_t v_inconsistent_2474_; lean_object* v_nextIdx_2475_; lean_object* v_newRawFacts_2476_; lean_object* v_facts_2477_; lean_object* v_extThms_2478_; lean_object* v_inj_2479_; lean_object* v_split_2480_; lean_object* v_clean_2481_; lean_object* v_sstates_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2514_; 
v_nextDeclIdx_2466_ = lean_ctor_get(v_toGoalState_2460_, 0);
v_enodeMap_2467_ = lean_ctor_get(v_toGoalState_2460_, 1);
v_exprs_2468_ = lean_ctor_get(v_toGoalState_2460_, 2);
v_parents_2469_ = lean_ctor_get(v_toGoalState_2460_, 3);
v_congrTable_2470_ = lean_ctor_get(v_toGoalState_2460_, 4);
v_appMap_2471_ = lean_ctor_get(v_toGoalState_2460_, 5);
v_indicesFound_2472_ = lean_ctor_get(v_toGoalState_2460_, 6);
v_newFacts_2473_ = lean_ctor_get(v_toGoalState_2460_, 7);
v_inconsistent_2474_ = lean_ctor_get_uint8(v_toGoalState_2460_, sizeof(void*)*17);
v_nextIdx_2475_ = lean_ctor_get(v_toGoalState_2460_, 8);
v_newRawFacts_2476_ = lean_ctor_get(v_toGoalState_2460_, 9);
v_facts_2477_ = lean_ctor_get(v_toGoalState_2460_, 10);
v_extThms_2478_ = lean_ctor_get(v_toGoalState_2460_, 11);
v_inj_2479_ = lean_ctor_get(v_toGoalState_2460_, 13);
v_split_2480_ = lean_ctor_get(v_toGoalState_2460_, 14);
v_clean_2481_ = lean_ctor_get(v_toGoalState_2460_, 15);
v_sstates_2482_ = lean_ctor_get(v_toGoalState_2460_, 16);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_toGoalState_2460_);
if (v_isSharedCheck_2514_ == 0)
{
lean_object* v_unused_2515_; 
v_unused_2515_ = lean_ctor_get(v_toGoalState_2460_, 12);
lean_dec(v_unused_2515_);
v___x_2484_ = v_toGoalState_2460_;
v_isShared_2485_ = v_isSharedCheck_2514_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_sstates_2482_);
lean_inc(v_clean_2481_);
lean_inc(v_split_2480_);
lean_inc(v_inj_2479_);
lean_inc(v_extThms_2478_);
lean_inc(v_facts_2477_);
lean_inc(v_newRawFacts_2476_);
lean_inc(v_nextIdx_2475_);
lean_inc(v_newFacts_2473_);
lean_inc(v_indicesFound_2472_);
lean_inc(v_appMap_2471_);
lean_inc(v_congrTable_2470_);
lean_inc(v_parents_2469_);
lean_inc(v_exprs_2468_);
lean_inc(v_enodeMap_2467_);
lean_inc(v_nextDeclIdx_2466_);
lean_dec(v_toGoalState_2460_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2514_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v_thmMap_2486_; lean_object* v_gmt_2487_; lean_object* v_thms_2488_; lean_object* v_newThms_2489_; lean_object* v_numInstances_2490_; lean_object* v_numDelayedInstances_2491_; lean_object* v_num_2492_; lean_object* v_preInstances_2493_; lean_object* v_nextThmIdx_2494_; lean_object* v_matchEqNames_2495_; lean_object* v_delayedThmInsts_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2513_; 
v_thmMap_2486_ = lean_ctor_get(v_ematch_2461_, 0);
v_gmt_2487_ = lean_ctor_get(v_ematch_2461_, 1);
v_thms_2488_ = lean_ctor_get(v_ematch_2461_, 2);
v_newThms_2489_ = lean_ctor_get(v_ematch_2461_, 3);
v_numInstances_2490_ = lean_ctor_get(v_ematch_2461_, 4);
v_numDelayedInstances_2491_ = lean_ctor_get(v_ematch_2461_, 5);
v_num_2492_ = lean_ctor_get(v_ematch_2461_, 6);
v_preInstances_2493_ = lean_ctor_get(v_ematch_2461_, 7);
v_nextThmIdx_2494_ = lean_ctor_get(v_ematch_2461_, 8);
v_matchEqNames_2495_ = lean_ctor_get(v_ematch_2461_, 9);
v_delayedThmInsts_2496_ = lean_ctor_get(v_ematch_2461_, 10);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_ematch_2461_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2498_ = v_ematch_2461_;
v_isShared_2499_ = v_isSharedCheck_2513_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_delayedThmInsts_2496_);
lean_inc(v_matchEqNames_2495_);
lean_inc(v_nextThmIdx_2494_);
lean_inc(v_preInstances_2493_);
lean_inc(v_num_2492_);
lean_inc(v_numDelayedInstances_2491_);
lean_inc(v_numInstances_2490_);
lean_inc(v_newThms_2489_);
lean_inc(v_thms_2488_);
lean_inc(v_gmt_2487_);
lean_inc(v_thmMap_2486_);
lean_dec(v_ematch_2461_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2513_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2500_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2496_, v_head_2450_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 10, v___x_2500_);
v___x_2502_ = v___x_2498_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_thmMap_2486_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_gmt_2487_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_thms_2488_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_newThms_2489_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_numInstances_2490_);
lean_ctor_set(v_reuseFailAlloc_2512_, 5, v_numDelayedInstances_2491_);
lean_ctor_set(v_reuseFailAlloc_2512_, 6, v_num_2492_);
lean_ctor_set(v_reuseFailAlloc_2512_, 7, v_preInstances_2493_);
lean_ctor_set(v_reuseFailAlloc_2512_, 8, v_nextThmIdx_2494_);
lean_ctor_set(v_reuseFailAlloc_2512_, 9, v_matchEqNames_2495_);
lean_ctor_set(v_reuseFailAlloc_2512_, 10, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2504_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 12, v___x_2502_);
v___x_2504_ = v___x_2484_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_nextDeclIdx_2466_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_enodeMap_2467_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_exprs_2468_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_parents_2469_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v_congrTable_2470_);
lean_ctor_set(v_reuseFailAlloc_2511_, 5, v_appMap_2471_);
lean_ctor_set(v_reuseFailAlloc_2511_, 6, v_indicesFound_2472_);
lean_ctor_set(v_reuseFailAlloc_2511_, 7, v_newFacts_2473_);
lean_ctor_set(v_reuseFailAlloc_2511_, 8, v_nextIdx_2475_);
lean_ctor_set(v_reuseFailAlloc_2511_, 9, v_newRawFacts_2476_);
lean_ctor_set(v_reuseFailAlloc_2511_, 10, v_facts_2477_);
lean_ctor_set(v_reuseFailAlloc_2511_, 11, v_extThms_2478_);
lean_ctor_set(v_reuseFailAlloc_2511_, 12, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2511_, 13, v_inj_2479_);
lean_ctor_set(v_reuseFailAlloc_2511_, 14, v_split_2480_);
lean_ctor_set(v_reuseFailAlloc_2511_, 15, v_clean_2481_);
lean_ctor_set(v_reuseFailAlloc_2511_, 16, v_sstates_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*17, v_inconsistent_2474_);
v___x_2504_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2506_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2504_);
v___x_2506_ = v___x_2464_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_mvarId_2462_);
v___x_2506_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_st_ref_set(v___y_2438_, v___x_2506_);
v___x_2508_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2458_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_dec_ref_known(v___x_2508_, 1);
v_as_x27_2436_ = v_tail_2451_;
v_b_2437_ = v___x_2456_;
goto _start;
}
else
{
return v___x_2508_;
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
lean_dec(v___x_2457_);
v_as_x27_2436_ = v_tail_2451_;
v_b_2437_ = v___x_2456_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2519_, lean_object* v_b_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2519_, v_b_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec(v_as_x27_2519_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2534_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2574_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2574_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2574_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
uint8_t v___x_2550_; 
v___x_2550_ = lean_unbox(v_a_2546_);
lean_dec(v_a_2546_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v_toGoalState_2552_; lean_object* v_ematch_2553_; lean_object* v_delayedThmInsts_2554_; uint8_t v___x_2555_; 
v___x_2551_ = lean_st_ref_get(v_a_2534_);
v_toGoalState_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc_ref(v_toGoalState_2552_);
lean_dec(v___x_2551_);
v_ematch_2553_ = lean_ctor_get(v_toGoalState_2552_, 12);
lean_inc_ref(v_ematch_2553_);
lean_dec_ref(v_toGoalState_2552_);
v_delayedThmInsts_2554_ = lean_ctor_get(v_ematch_2553_, 10);
lean_inc_ref(v_delayedThmInsts_2554_);
lean_dec_ref(v_ematch_2553_);
v___x_2555_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2554_);
lean_dec_ref(v_delayedThmInsts_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_del_object(v___x_2548_);
v___x_2556_ = lean_box(0);
v___x_2557_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2533_, v___x_2556_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2564_ == 0)
{
lean_object* v_unused_2565_; 
v_unused_2565_ = lean_ctor_get(v___x_2557_, 0);
lean_dec(v_unused_2565_);
v___x_2559_ = v___x_2557_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v___x_2557_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2556_);
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2556_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
return v___x_2557_;
}
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2566_ = lean_box(0);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2566_);
v___x_2568_ = v___x_2548_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
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
lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2570_ = lean_box(0);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2570_);
v___x_2572_ = v___x_2548_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_a_2575_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2545_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2545_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec(v_toPropagateDown_2583_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2596_, lean_object* v_x_2597_, lean_object* v_x_2598_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2597_, v_x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2600_, lean_object* v_x_2601_, lean_object* v_x_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2600_, v_x_2601_, v_x_2602_);
lean_dec_ref(v_x_2602_);
lean_dec_ref(v_x_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2604_, lean_object* v_x_2605_, lean_object* v_x_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2605_, v_x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2608_, lean_object* v_x_2609_, lean_object* v_x_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2608_, v_x_2609_, v_x_2610_);
lean_dec_ref(v_x_2610_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2612_, lean_object* v_as_x27_2613_, lean_object* v_b_2614_, lean_object* v_a_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v___x_2627_; 
v___x_2627_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2613_, v_b_2614_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
return v___x_2627_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2628_, lean_object* v_as_x27_2629_, lean_object* v_b_2630_, lean_object* v_a_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2628_, v_as_x27_2629_, v_b_2630_, v_a_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec(v_as_x27_2629_);
lean_dec(v_as_2628_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2644_, lean_object* v_x_2645_, size_t v_x_2646_, lean_object* v_x_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2645_, v_x_2646_, v_x_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2649_, lean_object* v_x_2650_, lean_object* v_x_2651_, lean_object* v_x_2652_){
_start:
{
size_t v_x_22439__boxed_2653_; lean_object* v_res_2654_; 
v_x_22439__boxed_2653_ = lean_unbox_usize(v_x_2651_);
lean_dec(v_x_2651_);
v_res_2654_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2649_, v_x_2650_, v_x_22439__boxed_2653_, v_x_2652_);
lean_dec_ref(v_x_2652_);
lean_dec_ref(v_x_2650_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2655_, lean_object* v_x_2656_, size_t v_x_2657_, lean_object* v_x_2658_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2656_, v_x_2657_, v_x_2658_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_, lean_object* v_x_2663_){
_start:
{
size_t v_x_22450__boxed_2664_; lean_object* v_res_2665_; 
v_x_22450__boxed_2664_ = lean_unbox_usize(v_x_2662_);
lean_dec(v_x_2662_);
v_res_2665_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2660_, v_x_2661_, v_x_22450__boxed_2664_, v_x_2663_);
lean_dec_ref(v_x_2663_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2666_, lean_object* v_keys_2667_, lean_object* v_vals_2668_, lean_object* v_heq_2669_, lean_object* v_i_2670_, lean_object* v_k_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2667_, v_vals_2668_, v_i_2670_, v_k_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2673_, lean_object* v_keys_2674_, lean_object* v_vals_2675_, lean_object* v_heq_2676_, lean_object* v_i_2677_, lean_object* v_k_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2673_, v_keys_2674_, v_vals_2675_, v_heq_2676_, v_i_2677_, v_k_2678_);
lean_dec_ref(v_k_2678_);
lean_dec_ref(v_vals_2675_);
lean_dec_ref(v_keys_2674_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2680_, lean_object* v_keys_2681_, lean_object* v_vals_2682_, lean_object* v_i_2683_, lean_object* v_k_2684_){
_start:
{
lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2685_ = lean_array_get_size(v_keys_2681_);
v___x_2686_ = lean_nat_dec_lt(v_i_2683_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; 
lean_dec_ref(v_k_2684_);
lean_dec(v_i_2683_);
v___x_2687_ = lean_box(0);
return v___x_2687_;
}
else
{
lean_object* v_k_x27_2688_; uint8_t v___x_2689_; 
v_k_x27_2688_ = lean_array_fget_borrowed(v_keys_2681_, v_i_2683_);
lean_inc(v_k_x27_2688_);
lean_inc_ref(v_k_2684_);
v___x_2689_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2680_, v_k_2684_, v_k_x27_2688_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_unsigned_to_nat(1u);
v___x_2691_ = lean_nat_add(v_i_2683_, v___x_2690_);
lean_dec(v_i_2683_);
v_i_2683_ = v___x_2691_;
goto _start;
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_dec_ref(v_k_2684_);
v___x_2693_ = lean_array_fget_borrowed(v_vals_2682_, v_i_2683_);
lean_dec(v_i_2683_);
lean_inc(v___x_2693_);
lean_inc(v_k_x27_2688_);
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v_k_x27_2688_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2696_, lean_object* v_keys_2697_, lean_object* v_vals_2698_, lean_object* v_i_2699_, lean_object* v_k_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2696_, v_keys_2697_, v_vals_2698_, v_i_2699_, v_k_2700_);
lean_dec_ref(v_vals_2698_);
lean_dec_ref(v_keys_2697_);
lean_dec_ref(v___x_2696_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2702_, lean_object* v_x_2703_, size_t v_x_2704_, lean_object* v_x_2705_){
_start:
{
if (lean_obj_tag(v_x_2703_) == 0)
{
lean_object* v_es_2706_; lean_object* v___x_2707_; size_t v___x_2708_; size_t v___x_2709_; lean_object* v_j_2710_; lean_object* v___x_2711_; 
v_es_2706_ = lean_ctor_get(v_x_2703_, 0);
lean_inc_ref(v_es_2706_);
lean_dec_ref_known(v_x_2703_, 1);
v___x_2707_ = lean_box(2);
v___x_2708_ = ((size_t)31ULL);
v___x_2709_ = lean_usize_land(v_x_2704_, v___x_2708_);
v_j_2710_ = lean_usize_to_nat(v___x_2709_);
v___x_2711_ = lean_array_get(v___x_2707_, v_es_2706_, v_j_2710_);
lean_dec(v_j_2710_);
lean_dec_ref(v_es_2706_);
switch(lean_obj_tag(v___x_2711_))
{
case 0:
{
lean_object* v_key_2712_; lean_object* v_val_2713_; uint8_t v___x_2714_; 
v_key_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc_n(v_key_2712_, 2);
v_val_2713_ = lean_ctor_get(v___x_2711_, 1);
lean_inc(v_val_2713_);
lean_dec_ref_known(v___x_2711_, 2);
v___x_2714_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2702_, v_x_2705_, v_key_2712_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; 
lean_dec(v_val_2713_);
lean_dec(v_key_2712_);
v___x_2715_ = lean_box(0);
return v___x_2715_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_key_2712_);
lean_ctor_set(v___x_2716_, 1, v_val_2713_);
v___x_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
return v___x_2717_;
}
}
case 1:
{
lean_object* v_node_2718_; size_t v___x_2719_; size_t v___x_2720_; 
v_node_2718_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_node_2718_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2719_ = ((size_t)5ULL);
v___x_2720_ = lean_usize_shift_right(v_x_2704_, v___x_2719_);
v_x_2703_ = v_node_2718_;
v_x_2704_ = v___x_2720_;
goto _start;
}
default: 
{
lean_object* v___x_2722_; 
lean_dec_ref(v_x_2705_);
v___x_2722_ = lean_box(0);
return v___x_2722_;
}
}
}
else
{
lean_object* v_ks_2723_; lean_object* v_vs_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_ks_2723_ = lean_ctor_get(v_x_2703_, 0);
lean_inc_ref(v_ks_2723_);
v_vs_2724_ = lean_ctor_get(v_x_2703_, 1);
lean_inc_ref(v_vs_2724_);
lean_dec_ref_known(v_x_2703_, 2);
v___x_2725_ = lean_unsigned_to_nat(0u);
v___x_2726_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2702_, v_ks_2723_, v_vs_2724_, v___x_2725_, v_x_2705_);
lean_dec_ref(v_vs_2724_);
lean_dec_ref(v_ks_2723_);
return v___x_2726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_){
_start:
{
size_t v_x_27612__boxed_2731_; lean_object* v_res_2732_; 
v_x_27612__boxed_2731_ = lean_unbox_usize(v_x_2729_);
lean_dec(v_x_2729_);
v_res_2732_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2727_, v_x_2728_, v_x_27612__boxed_2731_, v_x_2730_);
lean_dec_ref(v___x_2727_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2733_, lean_object* v_x_2734_, lean_object* v_x_2735_){
_start:
{
uint64_t v___x_2736_; size_t v___x_2737_; lean_object* v___x_2738_; 
lean_inc_ref(v_x_2735_);
v___x_2736_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2733_, v_x_2735_);
v___x_2737_ = lean_uint64_to_usize(v___x_2736_);
lean_inc_ref(v_x_2734_);
v___x_2738_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2733_, v_x_2734_, v___x_2737_, v_x_2735_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2739_, lean_object* v_x_2740_, lean_object* v_x_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2739_, v_x_2740_, v_x_2741_);
lean_dec_ref(v_x_2740_);
lean_dec_ref(v___x_2739_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2743_, lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_, lean_object* v_x_2747_){
_start:
{
lean_object* v_ks_2748_; lean_object* v_vs_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2773_; 
v_ks_2748_ = lean_ctor_get(v_x_2744_, 0);
v_vs_2749_ = lean_ctor_get(v_x_2744_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_x_2744_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2751_ = v_x_2744_;
v_isShared_2752_ = v_isSharedCheck_2773_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_vs_2749_);
lean_inc(v_ks_2748_);
lean_dec(v_x_2744_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2773_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = lean_array_get_size(v_ks_2748_);
v___x_2754_ = lean_nat_dec_lt(v_x_2745_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
lean_dec(v_x_2745_);
v___x_2755_ = lean_array_push(v_ks_2748_, v_x_2746_);
v___x_2756_ = lean_array_push(v_vs_2749_, v_x_2747_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 1, v___x_2756_);
lean_ctor_set(v___x_2751_, 0, v___x_2755_);
v___x_2758_ = v___x_2751_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
else
{
lean_object* v_k_x27_2760_; uint8_t v___x_2761_; 
v_k_x27_2760_ = lean_array_fget_borrowed(v_ks_2748_, v_x_2745_);
lean_inc(v_k_x27_2760_);
lean_inc_ref(v_x_2746_);
v___x_2761_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2743_, v_x_2746_, v_k_x27_2760_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2763_; 
if (v_isShared_2752_ == 0)
{
v___x_2763_ = v___x_2751_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_ks_2748_);
lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_vs_2749_);
v___x_2763_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_unsigned_to_nat(1u);
v___x_2765_ = lean_nat_add(v_x_2745_, v___x_2764_);
lean_dec(v_x_2745_);
v_x_2744_ = v___x_2763_;
v_x_2745_ = v___x_2765_;
goto _start;
}
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2768_ = lean_array_fset(v_ks_2748_, v_x_2745_, v_x_2746_);
v___x_2769_ = lean_array_fset(v_vs_2749_, v_x_2745_, v_x_2747_);
lean_dec(v_x_2745_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 1, v___x_2769_);
lean_ctor_set(v___x_2751_, 0, v___x_2768_);
v___x_2771_ = v___x_2751_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2774_, lean_object* v_x_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2774_, v_x_2775_, v_x_2776_, v_x_2777_, v_x_2778_);
lean_dec_ref(v___x_2774_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2780_, lean_object* v_n_2781_, lean_object* v_k_2782_, lean_object* v_v_2783_){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_unsigned_to_nat(0u);
v___x_2785_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2780_, v_n_2781_, v___x_2784_, v_k_2782_, v_v_2783_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2786_, lean_object* v_n_2787_, lean_object* v_k_2788_, lean_object* v_v_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2786_, v_n_2787_, v_k_2788_, v_v_2789_);
lean_dec_ref(v___x_2786_);
return v_res_2790_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2792_, lean_object* v_x_2793_, size_t v_x_2794_, size_t v_x_2795_, lean_object* v_x_2796_, lean_object* v_x_2797_){
_start:
{
if (lean_obj_tag(v_x_2793_) == 0)
{
lean_object* v_es_2798_; size_t v___x_2799_; size_t v___x_2800_; lean_object* v_j_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v_es_2798_ = lean_ctor_get(v_x_2793_, 0);
v___x_2799_ = ((size_t)31ULL);
v___x_2800_ = lean_usize_land(v_x_2794_, v___x_2799_);
v_j_2801_ = lean_usize_to_nat(v___x_2800_);
v___x_2802_ = lean_array_get_size(v_es_2798_);
v___x_2803_ = lean_nat_dec_lt(v_j_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_dec(v_j_2801_);
lean_dec(v_x_2797_);
lean_dec_ref(v_x_2796_);
return v_x_2793_;
}
else
{
lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2842_; 
lean_inc_ref(v_es_2798_);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_x_2793_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v_x_2793_, 0);
lean_dec(v_unused_2843_);
v___x_2805_ = v_x_2793_;
v_isShared_2806_ = v_isSharedCheck_2842_;
goto v_resetjp_2804_;
}
else
{
lean_dec(v_x_2793_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2842_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v_v_2807_; lean_object* v___x_2808_; lean_object* v_xs_x27_2809_; lean_object* v___y_2811_; 
v_v_2807_ = lean_array_fget(v_es_2798_, v_j_2801_);
v___x_2808_ = lean_box(0);
v_xs_x27_2809_ = lean_array_fset(v_es_2798_, v_j_2801_, v___x_2808_);
switch(lean_obj_tag(v_v_2807_))
{
case 0:
{
lean_object* v_key_2816_; lean_object* v_val_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2827_; 
v_key_2816_ = lean_ctor_get(v_v_2807_, 0);
v_val_2817_ = lean_ctor_get(v_v_2807_, 1);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_v_2807_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2819_ = v_v_2807_;
v_isShared_2820_ = v_isSharedCheck_2827_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_val_2817_);
lean_inc(v_key_2816_);
lean_dec(v_v_2807_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2827_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
uint8_t v___x_2821_; 
lean_inc(v_key_2816_);
lean_inc_ref(v_x_2796_);
v___x_2821_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2792_, v_x_2796_, v_key_2816_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
lean_del_object(v___x_2819_);
v___x_2822_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2816_, v_val_2817_, v_x_2796_, v_x_2797_);
v___x_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
v___y_2811_ = v___x_2823_;
goto v___jp_2810_;
}
else
{
lean_object* v___x_2825_; 
lean_dec(v_val_2817_);
lean_dec(v_key_2816_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 1, v_x_2797_);
lean_ctor_set(v___x_2819_, 0, v_x_2796_);
v___x_2825_ = v___x_2819_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_x_2796_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_x_2797_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
v___y_2811_ = v___x_2825_;
goto v___jp_2810_;
}
}
}
}
case 1:
{
lean_object* v_node_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2840_; 
v_node_2828_ = lean_ctor_get(v_v_2807_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_v_2807_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2830_ = v_v_2807_;
v_isShared_2831_ = v_isSharedCheck_2840_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_node_2828_);
lean_dec(v_v_2807_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2840_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
size_t v___x_2832_; size_t v___x_2833_; size_t v___x_2834_; size_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2832_ = ((size_t)5ULL);
v___x_2833_ = lean_usize_shift_right(v_x_2794_, v___x_2832_);
v___x_2834_ = ((size_t)1ULL);
v___x_2835_ = lean_usize_add(v_x_2795_, v___x_2834_);
v___x_2836_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2792_, v_node_2828_, v___x_2833_, v___x_2835_, v_x_2796_, v_x_2797_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2836_);
v___x_2838_ = v___x_2830_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
v___y_2811_ = v___x_2838_;
goto v___jp_2810_;
}
}
}
default: 
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v_x_2796_);
lean_ctor_set(v___x_2841_, 1, v_x_2797_);
v___y_2811_ = v___x_2841_;
goto v___jp_2810_;
}
}
v___jp_2810_:
{
lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2812_ = lean_array_fset(v_xs_x27_2809_, v_j_2801_, v___y_2811_);
lean_dec(v_j_2801_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2812_);
v___x_2814_ = v___x_2805_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
else
{
lean_object* v_ks_2844_; lean_object* v_vs_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2865_; 
v_ks_2844_ = lean_ctor_get(v_x_2793_, 0);
v_vs_2845_ = lean_ctor_get(v_x_2793_, 1);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_x_2793_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2847_ = v_x_2793_;
v_isShared_2848_ = v_isSharedCheck_2865_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_vs_2845_);
lean_inc(v_ks_2844_);
lean_dec(v_x_2793_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2865_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_ks_2844_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_vs_2845_);
v___x_2850_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v_newNode_2851_; uint8_t v___y_2853_; size_t v___x_2859_; uint8_t v___x_2860_; 
v_newNode_2851_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2792_, v___x_2850_, v_x_2796_, v_x_2797_);
v___x_2859_ = ((size_t)7ULL);
v___x_2860_ = lean_usize_dec_le(v___x_2859_, v_x_2795_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2861_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2851_);
v___x_2862_ = lean_unsigned_to_nat(4u);
v___x_2863_ = lean_nat_dec_lt(v___x_2861_, v___x_2862_);
lean_dec(v___x_2861_);
v___y_2853_ = v___x_2863_;
goto v___jp_2852_;
}
else
{
v___y_2853_ = v___x_2860_;
goto v___jp_2852_;
}
v___jp_2852_:
{
if (v___y_2853_ == 0)
{
lean_object* v_ks_2854_; lean_object* v_vs_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_ks_2854_ = lean_ctor_get(v_newNode_2851_, 0);
lean_inc_ref(v_ks_2854_);
v_vs_2855_ = lean_ctor_get(v_newNode_2851_, 1);
lean_inc_ref(v_vs_2855_);
lean_dec_ref(v_newNode_2851_);
v___x_2856_ = lean_unsigned_to_nat(0u);
v___x_2857_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2858_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2792_, v_x_2795_, v_ks_2854_, v_vs_2855_, v___x_2856_, v___x_2857_);
lean_dec_ref(v_vs_2855_);
lean_dec_ref(v_ks_2854_);
return v___x_2858_;
}
else
{
return v_newNode_2851_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2866_, size_t v_depth_2867_, lean_object* v_keys_2868_, lean_object* v_vals_2869_, lean_object* v_i_2870_, lean_object* v_entries_2871_){
_start:
{
lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2872_ = lean_array_get_size(v_keys_2868_);
v___x_2873_ = lean_nat_dec_lt(v_i_2870_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_dec(v_i_2870_);
return v_entries_2871_;
}
else
{
lean_object* v_k_2874_; lean_object* v_v_2875_; uint64_t v___x_2876_; size_t v_h_2877_; size_t v___x_2878_; lean_object* v___x_2879_; size_t v___x_2880_; size_t v___x_2881_; size_t v___x_2882_; size_t v_h_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_k_2874_ = lean_array_fget_borrowed(v_keys_2868_, v_i_2870_);
v_v_2875_ = lean_array_fget_borrowed(v_vals_2869_, v_i_2870_);
lean_inc_n(v_k_2874_, 2);
v___x_2876_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2866_, v_k_2874_);
v_h_2877_ = lean_uint64_to_usize(v___x_2876_);
v___x_2878_ = ((size_t)5ULL);
v___x_2879_ = lean_unsigned_to_nat(1u);
v___x_2880_ = ((size_t)1ULL);
v___x_2881_ = lean_usize_sub(v_depth_2867_, v___x_2880_);
v___x_2882_ = lean_usize_mul(v___x_2878_, v___x_2881_);
v_h_2883_ = lean_usize_shift_right(v_h_2877_, v___x_2882_);
v___x_2884_ = lean_nat_add(v_i_2870_, v___x_2879_);
lean_dec(v_i_2870_);
lean_inc(v_v_2875_);
v___x_2885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2866_, v_entries_2871_, v_h_2883_, v_depth_2867_, v_k_2874_, v_v_2875_);
v_i_2870_ = v___x_2884_;
v_entries_2871_ = v___x_2885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2887_, lean_object* v_depth_2888_, lean_object* v_keys_2889_, lean_object* v_vals_2890_, lean_object* v_i_2891_, lean_object* v_entries_2892_){
_start:
{
size_t v_depth_boxed_2893_; lean_object* v_res_2894_; 
v_depth_boxed_2893_ = lean_unbox_usize(v_depth_2888_);
lean_dec(v_depth_2888_);
v_res_2894_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2887_, v_depth_boxed_2893_, v_keys_2889_, v_vals_2890_, v_i_2891_, v_entries_2892_);
lean_dec_ref(v_vals_2890_);
lean_dec_ref(v_keys_2889_);
lean_dec_ref(v___x_2887_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2895_, lean_object* v_x_2896_, lean_object* v_x_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
size_t v_x_27766__boxed_2901_; size_t v_x_27767__boxed_2902_; lean_object* v_res_2903_; 
v_x_27766__boxed_2901_ = lean_unbox_usize(v_x_2897_);
lean_dec(v_x_2897_);
v_x_27767__boxed_2902_ = lean_unbox_usize(v_x_2898_);
lean_dec(v_x_2898_);
v_res_2903_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2895_, v_x_2896_, v_x_27766__boxed_2901_, v_x_27767__boxed_2902_, v_x_2899_, v_x_2900_);
lean_dec_ref(v___x_2895_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_){
_start:
{
uint64_t v___x_2908_; size_t v___x_2909_; size_t v___x_2910_; lean_object* v___x_2911_; 
lean_inc_ref(v_x_2906_);
v___x_2908_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2904_, v_x_2906_);
v___x_2909_ = lean_uint64_to_usize(v___x_2908_);
v___x_2910_ = ((size_t)1ULL);
v___x_2911_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2904_, v_x_2905_, v___x_2909_, v___x_2910_, v_x_2906_, v_x_2907_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2912_, v_x_2913_, v_x_2914_, v_x_2915_);
lean_dec_ref(v___x_2912_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2921_, lean_object* v_rootNew_2922_, uint8_t v_a_2923_, lean_object* v_a_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; lean_object* v_snd_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_3100_; 
v___x_2932_ = lean_st_ref_get(v___y_2925_);
v_snd_2933_ = lean_ctor_get(v_a_2924_, 1);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_a_2924_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; 
v_unused_3101_ = lean_ctor_get(v_a_2924_, 0);
lean_dec(v_unused_3101_);
v___x_2935_ = v_a_2924_;
v_isShared_2936_ = v_isSharedCheck_3100_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_snd_2933_);
lean_dec(v_a_2924_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_3100_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; 
lean_inc(v_snd_2933_);
v___x_2937_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2932_, v_snd_2933_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___x_2932_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_3091_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_2940_ = v___x_2937_;
v_isShared_2941_ = v_isSharedCheck_3091_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_3091_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v_self_2942_; lean_object* v_next_2943_; lean_object* v_congr_2944_; lean_object* v_target_x3f_2945_; lean_object* v_proof_x3f_2946_; uint8_t v_flipped_2947_; lean_object* v_size_2948_; uint8_t v_interpreted_2949_; uint8_t v_ctor_2950_; uint8_t v_hasLambdas_2951_; uint8_t v_heqProofs_2952_; lean_object* v_idx_2953_; lean_object* v_generation_2954_; lean_object* v_mt_2955_; lean_object* v_sTerms_2956_; uint8_t v_funCC_2957_; lean_object* v_ematchDiagSource_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_3089_; 
v_self_2942_ = lean_ctor_get(v_a_2938_, 0);
v_next_2943_ = lean_ctor_get(v_a_2938_, 1);
v_congr_2944_ = lean_ctor_get(v_a_2938_, 3);
v_target_x3f_2945_ = lean_ctor_get(v_a_2938_, 4);
v_proof_x3f_2946_ = lean_ctor_get(v_a_2938_, 5);
v_flipped_2947_ = lean_ctor_get_uint8(v_a_2938_, sizeof(void*)*12);
v_size_2948_ = lean_ctor_get(v_a_2938_, 6);
v_interpreted_2949_ = lean_ctor_get_uint8(v_a_2938_, sizeof(void*)*12 + 1);
v_ctor_2950_ = lean_ctor_get_uint8(v_a_2938_, sizeof(void*)*12 + 2);
v_hasLambdas_2951_ = lean_ctor_get_uint8(v_a_2938_, sizeof(void*)*12 + 3);
v_heqProofs_2952_ = lean_ctor_get_uint8(v_a_2938_, sizeof(void*)*12 + 4);
v_idx_2953_ = lean_ctor_get(v_a_2938_, 7);
v_generation_2954_ = lean_ctor_get(v_a_2938_, 8);
v_mt_2955_ = lean_ctor_get(v_a_2938_, 9);
v_sTerms_2956_ = lean_ctor_get(v_a_2938_, 10);
v_funCC_2957_ = lean_ctor_get_uint8(v_a_2938_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2958_ = lean_ctor_get(v_a_2938_, 11);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v_a_2938_, 2);
lean_dec(v_unused_3090_);
v___x_2960_ = v_a_2938_;
v_isShared_2961_ = v_isSharedCheck_3089_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_ematchDiagSource_2958_);
lean_inc(v_sTerms_2956_);
lean_inc(v_mt_2955_);
lean_inc(v_generation_2954_);
lean_inc(v_idx_2953_);
lean_inc(v_size_2948_);
lean_inc(v_proof_x3f_2946_);
lean_inc(v_target_x3f_2945_);
lean_inc(v_congr_2944_);
lean_inc(v_next_2943_);
lean_inc(v_self_2942_);
lean_dec(v_a_2938_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_3089_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; lean_object* v___y_2977_; lean_object* v___x_2987_; 
v___x_2962_ = lean_box(0);
lean_inc(v_ematchDiagSource_2958_);
lean_inc(v_sTerms_2956_);
lean_inc(v_mt_2955_);
lean_inc(v_generation_2954_);
lean_inc(v_idx_2953_);
lean_inc(v_size_2948_);
lean_inc(v_proof_x3f_2946_);
lean_inc(v_target_x3f_2945_);
lean_inc_ref(v_rootNew_2922_);
lean_inc_ref(v_next_2943_);
lean_inc_ref(v_self_2942_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 2, v_rootNew_2922_);
v___x_2987_ = v___x_2960_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_self_2942_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_next_2943_);
lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_rootNew_2922_);
lean_ctor_set(v_reuseFailAlloc_3088_, 3, v_congr_2944_);
lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_target_x3f_2945_);
lean_ctor_set(v_reuseFailAlloc_3088_, 5, v_proof_x3f_2946_);
lean_ctor_set(v_reuseFailAlloc_3088_, 6, v_size_2948_);
lean_ctor_set(v_reuseFailAlloc_3088_, 7, v_idx_2953_);
lean_ctor_set(v_reuseFailAlloc_3088_, 8, v_generation_2954_);
lean_ctor_set(v_reuseFailAlloc_3088_, 9, v_mt_2955_);
lean_ctor_set(v_reuseFailAlloc_3088_, 10, v_sTerms_2956_);
lean_ctor_set(v_reuseFailAlloc_3088_, 11, v_ematchDiagSource_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3088_, sizeof(void*)*12, v_flipped_2947_);
lean_ctor_set_uint8(v_reuseFailAlloc_3088_, sizeof(void*)*12 + 1, v_interpreted_2949_);
lean_ctor_set_uint8(v_reuseFailAlloc_3088_, sizeof(void*)*12 + 2, v_ctor_2950_);
lean_ctor_set_uint8(v_reuseFailAlloc_3088_, sizeof(void*)*12 + 3, v_hasLambdas_2951_);
lean_ctor_set_uint8(v_reuseFailAlloc_3088_, sizeof(void*)*12 + 4, v_heqProofs_2952_);
lean_ctor_set_uint8(v_reuseFailAlloc_3088_, sizeof(void*)*12 + 5, v_funCC_2957_);
v___x_2987_ = v_reuseFailAlloc_3088_;
goto v_reusejp_2986_;
}
v___jp_2963_:
{
uint8_t v___x_2964_; 
v___x_2964_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_next_2943_, v_lhs_2921_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2966_; 
lean_del_object(v___x_2940_);
lean_dec(v_snd_2933_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 1, v_next_2943_);
lean_ctor_set(v___x_2935_, 0, v___x_2962_);
v___x_2966_ = v___x_2935_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2962_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_next_2943_);
v___x_2966_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
v_a_2924_ = v___x_2966_;
goto _start;
}
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
lean_dec_ref(v_next_2943_);
lean_dec_ref(v_rootNew_2922_);
v___x_2969_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v___x_2969_);
v___x_2971_ = v___x_2935_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_snd_2933_);
v___x_2971_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2973_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v___x_2971_);
v___x_2973_ = v___x_2940_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
v___jp_2976_:
{
if (lean_obj_tag(v___y_2977_) == 0)
{
lean_dec_ref_known(v___y_2977_, 1);
goto v___jp_2963_;
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec_ref(v_next_2943_);
lean_del_object(v___x_2940_);
lean_del_object(v___x_2935_);
lean_dec(v_snd_2933_);
lean_dec_ref(v_rootNew_2922_);
v_a_2978_ = lean_ctor_get(v___y_2977_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___y_2977_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___y_2977_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___y_2977_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
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
lean_inc_ref(v_self_2942_);
v___x_2988_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2942_, v___x_2987_, v___y_2925_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_dec_ref_known(v___x_2988_, 1);
if (v_a_2923_ == 0)
{
lean_dec_ref(v___x_2987_);
lean_dec(v_ematchDiagSource_2958_);
lean_dec(v_sTerms_2956_);
lean_dec(v_mt_2955_);
lean_dec(v_generation_2954_);
lean_dec(v_idx_2953_);
lean_dec(v_size_2948_);
lean_dec(v_proof_x3f_2946_);
lean_dec(v_target_x3f_2945_);
lean_dec_ref(v_self_2942_);
goto v___jp_2963_;
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v___x_2989_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2990_ = lean_unsigned_to_nat(3u);
v___x_2991_ = l_Lean_Expr_isAppOfArity(v_self_2942_, v___x_2989_, v___x_2990_);
if (v___x_2991_ == 0)
{
lean_dec_ref(v___x_2987_);
lean_dec(v_ematchDiagSource_2958_);
lean_dec(v_sTerms_2956_);
lean_dec(v_mt_2955_);
lean_dec(v_generation_2954_);
lean_dec(v_idx_2953_);
lean_dec(v_size_2948_);
lean_dec(v_proof_x3f_2946_);
lean_dec(v_target_x3f_2945_);
lean_dec_ref(v_self_2942_);
goto v___jp_2963_;
}
else
{
uint8_t v___x_2992_; 
v___x_2992_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2987_);
lean_dec_ref(v___x_2987_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; lean_object* v_toGoalState_2994_; lean_object* v_enodeMap_2995_; lean_object* v_congrTable_2996_; lean_object* v___x_2997_; 
v___x_2993_ = lean_st_ref_get(v___y_2925_);
v_toGoalState_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc_ref(v_toGoalState_2994_);
lean_dec(v___x_2993_);
v_enodeMap_2995_ = lean_ctor_get(v_toGoalState_2994_, 1);
lean_inc_ref(v_enodeMap_2995_);
v_congrTable_2996_ = lean_ctor_get(v_toGoalState_2994_, 4);
lean_inc_ref(v_congrTable_2996_);
lean_dec_ref(v_toGoalState_2994_);
lean_inc_ref(v_self_2942_);
v___x_2997_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_2995_, v_congrTable_2996_, v_self_2942_);
lean_dec_ref(v_congrTable_2996_);
lean_dec_ref(v_enodeMap_2995_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_dec(v_ematchDiagSource_2958_);
lean_dec(v_sTerms_2956_);
lean_dec(v_mt_2955_);
lean_dec(v_generation_2954_);
lean_dec(v_idx_2953_);
lean_dec(v_size_2948_);
lean_dec(v_proof_x3f_2946_);
lean_dec(v_target_x3f_2945_);
lean_dec_ref(v_self_2942_);
goto v___jp_2963_;
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
v___x_3000_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_2999_, v___y_2926_);
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
lean_object* v___x_3003_; lean_object* v_toGoalState_3004_; lean_object* v_mvarId_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3079_; 
v___x_3003_ = lean_st_ref_take(v___y_2925_);
v_toGoalState_3004_ = lean_ctor_get(v___x_3003_, 0);
v_mvarId_3005_ = lean_ctor_get(v___x_3003_, 1);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3007_ = v___x_3003_;
v_isShared_3008_ = v_isSharedCheck_3079_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_mvarId_3005_);
lean_inc(v_toGoalState_3004_);
lean_dec(v___x_3003_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3079_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v_nextDeclIdx_3009_; lean_object* v_enodeMap_3010_; lean_object* v_exprs_3011_; lean_object* v_parents_3012_; lean_object* v_congrTable_3013_; lean_object* v_appMap_3014_; lean_object* v_indicesFound_3015_; lean_object* v_newFacts_3016_; uint8_t v_inconsistent_3017_; lean_object* v_nextIdx_3018_; lean_object* v_newRawFacts_3019_; lean_object* v_facts_3020_; lean_object* v_extThms_3021_; lean_object* v_ematch_3022_; lean_object* v_inj_3023_; lean_object* v_split_3024_; lean_object* v_clean_3025_; lean_object* v_sstates_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3078_; 
v_nextDeclIdx_3009_ = lean_ctor_get(v_toGoalState_3004_, 0);
v_enodeMap_3010_ = lean_ctor_get(v_toGoalState_3004_, 1);
v_exprs_3011_ = lean_ctor_get(v_toGoalState_3004_, 2);
v_parents_3012_ = lean_ctor_get(v_toGoalState_3004_, 3);
v_congrTable_3013_ = lean_ctor_get(v_toGoalState_3004_, 4);
v_appMap_3014_ = lean_ctor_get(v_toGoalState_3004_, 5);
v_indicesFound_3015_ = lean_ctor_get(v_toGoalState_3004_, 6);
v_newFacts_3016_ = lean_ctor_get(v_toGoalState_3004_, 7);
v_inconsistent_3017_ = lean_ctor_get_uint8(v_toGoalState_3004_, sizeof(void*)*17);
v_nextIdx_3018_ = lean_ctor_get(v_toGoalState_3004_, 8);
v_newRawFacts_3019_ = lean_ctor_get(v_toGoalState_3004_, 9);
v_facts_3020_ = lean_ctor_get(v_toGoalState_3004_, 10);
v_extThms_3021_ = lean_ctor_get(v_toGoalState_3004_, 11);
v_ematch_3022_ = lean_ctor_get(v_toGoalState_3004_, 12);
v_inj_3023_ = lean_ctor_get(v_toGoalState_3004_, 13);
v_split_3024_ = lean_ctor_get(v_toGoalState_3004_, 14);
v_clean_3025_ = lean_ctor_get(v_toGoalState_3004_, 15);
v_sstates_3026_ = lean_ctor_get(v_toGoalState_3004_, 16);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_toGoalState_3004_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3028_ = v_toGoalState_3004_;
v_isShared_3029_ = v_isSharedCheck_3078_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_sstates_3026_);
lean_inc(v_clean_3025_);
lean_inc(v_split_3024_);
lean_inc(v_inj_3023_);
lean_inc(v_ematch_3022_);
lean_inc(v_extThms_3021_);
lean_inc(v_facts_3020_);
lean_inc(v_newRawFacts_3019_);
lean_inc(v_nextIdx_3018_);
lean_inc(v_newFacts_3016_);
lean_inc(v_indicesFound_3015_);
lean_inc(v_appMap_3014_);
lean_inc(v_congrTable_3013_);
lean_inc(v_parents_3012_);
lean_inc(v_exprs_3011_);
lean_inc(v_enodeMap_3010_);
lean_inc(v_nextDeclIdx_3009_);
lean_dec(v_toGoalState_3004_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3078_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3030_ = lean_box(0);
lean_inc_ref(v_self_2942_);
v___x_3031_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3010_, v_congrTable_3013_, v_self_2942_, v___x_3030_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v___x_3031_);
v___x_3033_ = v___x_3028_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_nextDeclIdx_3009_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v_enodeMap_3010_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_exprs_3011_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v_parents_3012_);
lean_ctor_set(v_reuseFailAlloc_3077_, 4, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3077_, 5, v_appMap_3014_);
lean_ctor_set(v_reuseFailAlloc_3077_, 6, v_indicesFound_3015_);
lean_ctor_set(v_reuseFailAlloc_3077_, 7, v_newFacts_3016_);
lean_ctor_set(v_reuseFailAlloc_3077_, 8, v_nextIdx_3018_);
lean_ctor_set(v_reuseFailAlloc_3077_, 9, v_newRawFacts_3019_);
lean_ctor_set(v_reuseFailAlloc_3077_, 10, v_facts_3020_);
lean_ctor_set(v_reuseFailAlloc_3077_, 11, v_extThms_3021_);
lean_ctor_set(v_reuseFailAlloc_3077_, 12, v_ematch_3022_);
lean_ctor_set(v_reuseFailAlloc_3077_, 13, v_inj_3023_);
lean_ctor_set(v_reuseFailAlloc_3077_, 14, v_split_3024_);
lean_ctor_set(v_reuseFailAlloc_3077_, 15, v_clean_3025_);
lean_ctor_set(v_reuseFailAlloc_3077_, 16, v_sstates_3026_);
lean_ctor_set_uint8(v_reuseFailAlloc_3077_, sizeof(void*)*17, v_inconsistent_3017_);
v___x_3033_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3035_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3033_);
v___x_3035_ = v___x_3007_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_mvarId_3005_);
v___x_3035_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = lean_st_ref_set(v___y_2925_, v___x_3035_);
lean_inc_ref(v_rootNew_2922_);
lean_inc_ref(v_next_2943_);
lean_inc_ref_n(v_self_2942_, 3);
v___x_3037_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3037_, 0, v_self_2942_);
lean_ctor_set(v___x_3037_, 1, v_next_2943_);
lean_ctor_set(v___x_3037_, 2, v_rootNew_2922_);
lean_ctor_set(v___x_3037_, 3, v_self_2942_);
lean_ctor_set(v___x_3037_, 4, v_target_x3f_2945_);
lean_ctor_set(v___x_3037_, 5, v_proof_x3f_2946_);
lean_ctor_set(v___x_3037_, 6, v_size_2948_);
lean_ctor_set(v___x_3037_, 7, v_idx_2953_);
lean_ctor_set(v___x_3037_, 8, v_generation_2954_);
lean_ctor_set(v___x_3037_, 9, v_mt_2955_);
lean_ctor_set(v___x_3037_, 10, v_sTerms_2956_);
lean_ctor_set(v___x_3037_, 11, v_ematchDiagSource_2958_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*12, v_flipped_2947_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*12 + 1, v_interpreted_2949_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*12 + 2, v_ctor_2950_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*12 + 3, v_hasLambdas_2951_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*12 + 4, v_heqProofs_2952_);
lean_ctor_set_uint8(v___x_3037_, sizeof(void*)*12 + 5, v_funCC_2957_);
v___x_3038_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2942_, v___x_3037_, v___y_2925_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_dec_ref_known(v___x_3038_, 1);
v___x_3039_ = lean_st_ref_get(v___y_2925_);
lean_inc(v_fst_2999_);
v___x_3040_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3039_, v_fst_2999_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___x_3039_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v_self_3042_; lean_object* v_next_3043_; lean_object* v_root_3044_; lean_object* v_target_x3f_3045_; lean_object* v_proof_x3f_3046_; uint8_t v_flipped_3047_; lean_object* v_size_3048_; uint8_t v_interpreted_3049_; uint8_t v_ctor_3050_; uint8_t v_hasLambdas_3051_; uint8_t v_heqProofs_3052_; lean_object* v_idx_3053_; lean_object* v_generation_3054_; lean_object* v_mt_3055_; lean_object* v_sTerms_3056_; uint8_t v_funCC_3057_; lean_object* v_ematchDiagSource_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3066_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
v_self_3042_ = lean_ctor_get(v_a_3041_, 0);
v_next_3043_ = lean_ctor_get(v_a_3041_, 1);
v_root_3044_ = lean_ctor_get(v_a_3041_, 2);
v_target_x3f_3045_ = lean_ctor_get(v_a_3041_, 4);
v_proof_x3f_3046_ = lean_ctor_get(v_a_3041_, 5);
v_flipped_3047_ = lean_ctor_get_uint8(v_a_3041_, sizeof(void*)*12);
v_size_3048_ = lean_ctor_get(v_a_3041_, 6);
v_interpreted_3049_ = lean_ctor_get_uint8(v_a_3041_, sizeof(void*)*12 + 1);
v_ctor_3050_ = lean_ctor_get_uint8(v_a_3041_, sizeof(void*)*12 + 2);
v_hasLambdas_3051_ = lean_ctor_get_uint8(v_a_3041_, sizeof(void*)*12 + 3);
v_heqProofs_3052_ = lean_ctor_get_uint8(v_a_3041_, sizeof(void*)*12 + 4);
v_idx_3053_ = lean_ctor_get(v_a_3041_, 7);
v_generation_3054_ = lean_ctor_get(v_a_3041_, 8);
v_mt_3055_ = lean_ctor_get(v_a_3041_, 9);
v_sTerms_3056_ = lean_ctor_get(v_a_3041_, 10);
v_funCC_3057_ = lean_ctor_get_uint8(v_a_3041_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3058_ = lean_ctor_get(v_a_3041_, 11);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_a_3041_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; 
v_unused_3067_ = lean_ctor_get(v_a_3041_, 3);
lean_dec(v_unused_3067_);
v___x_3060_ = v_a_3041_;
v_isShared_3061_ = v_isSharedCheck_3066_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_ematchDiagSource_3058_);
lean_inc(v_sTerms_3056_);
lean_inc(v_mt_3055_);
lean_inc(v_generation_3054_);
lean_inc(v_idx_3053_);
lean_inc(v_size_3048_);
lean_inc(v_proof_x3f_3046_);
lean_inc(v_target_x3f_3045_);
lean_inc(v_root_3044_);
lean_inc(v_next_3043_);
lean_inc(v_self_3042_);
lean_dec(v_a_3041_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3066_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 3, v_self_2942_);
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_self_3042_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_next_3043_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_root_3044_);
lean_ctor_set(v_reuseFailAlloc_3065_, 3, v_self_2942_);
lean_ctor_set(v_reuseFailAlloc_3065_, 4, v_target_x3f_3045_);
lean_ctor_set(v_reuseFailAlloc_3065_, 5, v_proof_x3f_3046_);
lean_ctor_set(v_reuseFailAlloc_3065_, 6, v_size_3048_);
lean_ctor_set(v_reuseFailAlloc_3065_, 7, v_idx_3053_);
lean_ctor_set(v_reuseFailAlloc_3065_, 8, v_generation_3054_);
lean_ctor_set(v_reuseFailAlloc_3065_, 9, v_mt_3055_);
lean_ctor_set(v_reuseFailAlloc_3065_, 10, v_sTerms_3056_);
lean_ctor_set(v_reuseFailAlloc_3065_, 11, v_ematchDiagSource_3058_);
lean_ctor_set_uint8(v_reuseFailAlloc_3065_, sizeof(void*)*12, v_flipped_3047_);
lean_ctor_set_uint8(v_reuseFailAlloc_3065_, sizeof(void*)*12 + 1, v_interpreted_3049_);
lean_ctor_set_uint8(v_reuseFailAlloc_3065_, sizeof(void*)*12 + 2, v_ctor_3050_);
lean_ctor_set_uint8(v_reuseFailAlloc_3065_, sizeof(void*)*12 + 3, v_hasLambdas_3051_);
lean_ctor_set_uint8(v_reuseFailAlloc_3065_, sizeof(void*)*12 + 4, v_heqProofs_3052_);
lean_ctor_set_uint8(v_reuseFailAlloc_3065_, sizeof(void*)*12 + 5, v_funCC_3057_);
v___x_3063_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_2999_, v___x_3063_, v___y_2925_);
v___y_2977_ = v___x_3064_;
goto v___jp_2976_;
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v_fst_2999_);
lean_dec_ref(v_next_2943_);
lean_dec_ref(v_self_2942_);
lean_del_object(v___x_2940_);
lean_del_object(v___x_2935_);
lean_dec(v_snd_2933_);
lean_dec_ref(v_rootNew_2922_);
v_a_3068_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3040_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3040_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_dec(v_fst_2999_);
lean_dec_ref(v_self_2942_);
v___y_2977_ = v___x_3038_;
goto v___jp_2976_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2999_);
lean_dec(v_ematchDiagSource_2958_);
lean_dec(v_sTerms_2956_);
lean_dec(v_mt_2955_);
lean_dec(v_generation_2954_);
lean_dec(v_idx_2953_);
lean_dec(v_size_2948_);
lean_dec(v_proof_x3f_2946_);
lean_dec(v_target_x3f_2945_);
lean_dec_ref(v_self_2942_);
goto v___jp_2963_;
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v_fst_2999_);
lean_dec(v_ematchDiagSource_2958_);
lean_dec(v_sTerms_2956_);
lean_dec(v_mt_2955_);
lean_dec(v_generation_2954_);
lean_dec(v_idx_2953_);
lean_dec(v_size_2948_);
lean_dec(v_proof_x3f_2946_);
lean_dec(v_target_x3f_2945_);
lean_dec_ref(v_next_2943_);
lean_dec_ref(v_self_2942_);
lean_del_object(v___x_2940_);
lean_del_object(v___x_2935_);
lean_dec(v_snd_2933_);
lean_dec_ref(v_rootNew_2922_);
v_a_3080_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3000_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3000_);
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
else
{
lean_dec(v_ematchDiagSource_2958_);
lean_dec(v_sTerms_2956_);
lean_dec(v_mt_2955_);
lean_dec(v_generation_2954_);
lean_dec(v_idx_2953_);
lean_dec(v_size_2948_);
lean_dec(v_proof_x3f_2946_);
lean_dec(v_target_x3f_2945_);
lean_dec_ref(v_self_2942_);
goto v___jp_2963_;
}
}
}
}
else
{
lean_dec_ref(v___x_2987_);
lean_dec(v_ematchDiagSource_2958_);
lean_dec(v_sTerms_2956_);
lean_dec(v_mt_2955_);
lean_dec(v_generation_2954_);
lean_dec(v_idx_2953_);
lean_dec(v_size_2948_);
lean_dec(v_proof_x3f_2946_);
lean_dec(v_target_x3f_2945_);
lean_dec_ref(v_self_2942_);
v___y_2977_ = v___x_2988_;
goto v___jp_2976_;
}
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_del_object(v___x_2935_);
lean_dec(v_snd_2933_);
lean_dec_ref(v_rootNew_2922_);
v_a_3092_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_2937_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_2937_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3102_, lean_object* v_rootNew_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
uint8_t v_a_27954__boxed_3113_; lean_object* v_res_3114_; 
v_a_27954__boxed_3113_ = lean_unbox(v_a_3104_);
v_res_3114_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3102_, v_rootNew_3103_, v_a_27954__boxed_3113_, v_a_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v_lhs_3102_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3115_, lean_object* v_rootNew_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3116_, v_a_3121_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; lean_object* v___x_3133_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3128_, 1);
v___x_3130_ = lean_box(0);
lean_inc_ref(v_lhs_3115_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
lean_ctor_set(v___x_3131_, 1, v_lhs_3115_);
v___x_3132_ = lean_unbox(v_a_3129_);
lean_dec(v_a_3129_);
v___x_3133_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3115_, v_rootNew_3116_, v___x_3132_, v___x_3131_, v_a_3117_, v_a_3121_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_);
lean_dec_ref(v_lhs_3115_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3147_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3147_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3147_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v_fst_3138_; 
v_fst_3138_ = lean_ctor_get(v_a_3134_, 0);
lean_inc(v_fst_3138_);
lean_dec(v_a_3134_);
if (lean_obj_tag(v_fst_3138_) == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = lean_box(0);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3139_);
v___x_3141_ = v___x_3136_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
else
{
lean_object* v_val_3143_; lean_object* v___x_3145_; 
v_val_3143_ = lean_ctor_get(v_fst_3138_, 0);
lean_inc(v_val_3143_);
lean_dec_ref_known(v_fst_3138_, 1);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v_val_3143_);
v___x_3145_ = v___x_3136_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_val_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v_a_3148_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3133_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3133_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v_rootNew_3116_);
lean_dec_ref(v_lhs_3115_);
v_a_3156_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3128_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3128_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3164_, lean_object* v_rootNew_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3164_, v_rootNew_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
lean_dec(v_a_3173_);
lean_dec_ref(v_a_3172_);
lean_dec(v_a_3171_);
lean_dec_ref(v_a_3170_);
lean_dec(v_a_3169_);
lean_dec_ref(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec(v_a_3166_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3178_, lean_object* v_00_u03b2_3179_, lean_object* v_x_3180_, lean_object* v_x_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3178_, v_x_3180_, v_x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3183_, lean_object* v_00_u03b2_3184_, lean_object* v_x_3185_, lean_object* v_x_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3183_, v_00_u03b2_3184_, v_x_3185_, v_x_3186_);
lean_dec_ref(v_x_3185_);
lean_dec_ref(v___x_3183_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3188_, lean_object* v_00_u03b2_3189_, lean_object* v_x_3190_, lean_object* v_x_3191_, lean_object* v_x_3192_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3188_, v_x_3190_, v_x_3191_, v_x_3192_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3194_, lean_object* v_00_u03b2_3195_, lean_object* v_x_3196_, lean_object* v_x_3197_, lean_object* v_x_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3194_, v_00_u03b2_3195_, v_x_3196_, v_x_3197_, v_x_3198_);
lean_dec_ref(v___x_3194_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3200_, lean_object* v_rootNew_3201_, uint8_t v_a_3202_, lean_object* v_inst_3203_, lean_object* v_a_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3200_, v_rootNew_3201_, v_a_3202_, v_a_3204_, v___y_3205_, v___y_3209_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3217_, lean_object* v_rootNew_3218_, lean_object* v_a_3219_, lean_object* v_inst_3220_, lean_object* v_a_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
uint8_t v_a_28309__boxed_3233_; lean_object* v_res_3234_; 
v_a_28309__boxed_3233_ = lean_unbox(v_a_3219_);
v_res_3234_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3217_, v_rootNew_3218_, v_a_28309__boxed_3233_, v_inst_3220_, v_a_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v_lhs_3217_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3235_, lean_object* v_00_u03b2_3236_, lean_object* v_x_3237_, size_t v_x_3238_, lean_object* v_x_3239_){
_start:
{
lean_object* v___x_3240_; 
lean_inc_ref(v_x_3237_);
v___x_3240_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3235_, v_x_3237_, v_x_3238_, v_x_3239_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3241_, lean_object* v_00_u03b2_3242_, lean_object* v_x_3243_, lean_object* v_x_3244_, lean_object* v_x_3245_){
_start:
{
size_t v_x_28352__boxed_3246_; lean_object* v_res_3247_; 
v_x_28352__boxed_3246_ = lean_unbox_usize(v_x_3244_);
lean_dec(v_x_3244_);
v_res_3247_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3241_, v_00_u03b2_3242_, v_x_3243_, v_x_28352__boxed_3246_, v_x_3245_);
lean_dec_ref(v_x_3243_);
lean_dec_ref(v___x_3241_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3248_, lean_object* v_00_u03b2_3249_, lean_object* v_x_3250_, size_t v_x_3251_, size_t v_x_3252_, lean_object* v_x_3253_, lean_object* v_x_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3248_, v_x_3250_, v_x_3251_, v_x_3252_, v_x_3253_, v_x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3256_, lean_object* v_00_u03b2_3257_, lean_object* v_x_3258_, lean_object* v_x_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_, lean_object* v_x_3262_){
_start:
{
size_t v_x_28366__boxed_3263_; size_t v_x_28367__boxed_3264_; lean_object* v_res_3265_; 
v_x_28366__boxed_3263_ = lean_unbox_usize(v_x_3259_);
lean_dec(v_x_3259_);
v_x_28367__boxed_3264_ = lean_unbox_usize(v_x_3260_);
lean_dec(v_x_3260_);
v_res_3265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3256_, v_00_u03b2_3257_, v_x_3258_, v_x_28366__boxed_3263_, v_x_28367__boxed_3264_, v_x_3261_, v_x_3262_);
lean_dec_ref(v___x_3256_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3266_, lean_object* v_00_u03b2_3267_, lean_object* v_keys_3268_, lean_object* v_vals_3269_, lean_object* v_heq_3270_, lean_object* v_i_3271_, lean_object* v_k_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3266_, v_keys_3268_, v_vals_3269_, v_i_3271_, v_k_3272_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3274_, lean_object* v_00_u03b2_3275_, lean_object* v_keys_3276_, lean_object* v_vals_3277_, lean_object* v_heq_3278_, lean_object* v_i_3279_, lean_object* v_k_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3274_, v_00_u03b2_3275_, v_keys_3276_, v_vals_3277_, v_heq_3278_, v_i_3279_, v_k_3280_);
lean_dec_ref(v_vals_3277_);
lean_dec_ref(v_keys_3276_);
lean_dec_ref(v___x_3274_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3282_, lean_object* v_00_u03b2_3283_, lean_object* v_n_3284_, lean_object* v_k_3285_, lean_object* v_v_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3282_, v_n_3284_, v_k_3285_, v_v_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3288_, lean_object* v_00_u03b2_3289_, lean_object* v_n_3290_, lean_object* v_k_3291_, lean_object* v_v_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3288_, v_00_u03b2_3289_, v_n_3290_, v_k_3291_, v_v_3292_);
lean_dec_ref(v___x_3288_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3294_, lean_object* v_00_u03b2_3295_, size_t v_depth_3296_, lean_object* v_keys_3297_, lean_object* v_vals_3298_, lean_object* v_heq_3299_, lean_object* v_i_3300_, lean_object* v_entries_3301_){
_start:
{
lean_object* v___x_3302_; 
v___x_3302_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3294_, v_depth_3296_, v_keys_3297_, v_vals_3298_, v_i_3300_, v_entries_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3303_, lean_object* v_00_u03b2_3304_, lean_object* v_depth_3305_, lean_object* v_keys_3306_, lean_object* v_vals_3307_, lean_object* v_heq_3308_, lean_object* v_i_3309_, lean_object* v_entries_3310_){
_start:
{
size_t v_depth_boxed_3311_; lean_object* v_res_3312_; 
v_depth_boxed_3311_ = lean_unbox_usize(v_depth_3305_);
lean_dec(v_depth_3305_);
v_res_3312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3303_, v_00_u03b2_3304_, v_depth_boxed_3311_, v_keys_3306_, v_vals_3307_, v_heq_3308_, v_i_3309_, v_entries_3310_);
lean_dec_ref(v_vals_3307_);
lean_dec_ref(v_keys_3306_);
lean_dec_ref(v___x_3303_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3313_, lean_object* v_00_u03b2_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_, lean_object* v_x_3317_, lean_object* v_x_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3313_, v_x_3315_, v_x_3316_, v_x_3317_, v_x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3320_, lean_object* v_00_u03b2_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_, lean_object* v_x_3324_, lean_object* v_x_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3320_, v_00_u03b2_3321_, v_x_3322_, v_x_3323_, v_x_3324_, v_x_3325_);
lean_dec_ref(v___x_3320_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3327_, lean_object* v_b_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
if (lean_obj_tag(v_as_x27_3327_) == 0)
{
lean_object* v___x_3340_; 
v___x_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3340_, 0, v_b_3328_);
return v___x_3340_;
}
else
{
lean_object* v_head_3341_; lean_object* v_tail_3342_; lean_object* v___x_3343_; 
v_head_3341_ = lean_ctor_get(v_as_x27_3327_, 0);
v_tail_3342_ = lean_ctor_get(v_as_x27_3327_, 1);
lean_inc(v_head_3341_);
v___x_3343_ = l_Lean_Meta_Grind_propagateUp(v_head_3341_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v___x_3344_; 
lean_dec_ref_known(v___x_3343_, 1);
v___x_3344_ = lean_box(0);
v_as_x27_3327_ = v_tail_3342_;
v_b_3328_ = v___x_3344_;
goto _start;
}
else
{
return v___x_3343_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3346_, lean_object* v_b_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3346_, v_b_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec(v_as_x27_3346_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3360_, lean_object* v_b_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
if (lean_obj_tag(v_as_x27_3360_) == 0)
{
lean_object* v___x_3373_; 
v___x_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3373_, 0, v_b_3361_);
return v___x_3373_;
}
else
{
lean_object* v_head_3374_; lean_object* v_tail_3375_; lean_object* v___x_3376_; 
v_head_3374_ = lean_ctor_get(v_as_x27_3360_, 0);
v_tail_3375_ = lean_ctor_get(v_as_x27_3360_, 1);
lean_inc(v_head_3374_);
v___x_3376_ = l_Lean_Meta_Grind_propagateDown(v_head_3374_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v___x_3377_; 
lean_dec_ref_known(v___x_3376_, 1);
v___x_3377_ = lean_box(0);
v_as_x27_3360_ = v_tail_3375_;
v_b_3361_ = v___x_3377_;
goto _start;
}
else
{
return v___x_3376_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3379_, lean_object* v_b_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3379_, v_b_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec(v_as_x27_3379_);
return v_res_3392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_cls_3396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3397_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3398_ = l_Lean_Name_append(v___x_3397_, v_cls_3396_);
return v___x_3398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3401_ = l_Lean_stringToMessageData(v___x_3400_);
return v___x_3401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3404_ = l_Lean_stringToMessageData(v___x_3403_);
return v___x_3404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3411_, uint8_t v_isHEq_3412_, lean_object* v_lhs_3413_, lean_object* v_rhs_3414_, lean_object* v_lhsNode_3415_, lean_object* v_rhsNode_3416_, lean_object* v_lhsRoot_3417_, lean_object* v_rhsRoot_3418_, uint8_t v_flipped_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; uint8_t v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; uint8_t v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; uint8_t v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; uint8_t v___y_3510_; uint8_t v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; uint8_t v___y_3519_; lean_object* v___y_3549_; uint8_t v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; uint8_t v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; uint8_t v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; uint8_t v___y_3575_; uint8_t v___y_3576_; uint8_t v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; uint8_t v___y_3585_; uint8_t v___y_3587_; lean_object* v___y_3588_; uint8_t v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v_options_3669_; lean_object* v_inheritedTraceOptions_3670_; uint8_t v_hasTrace_3671_; lean_object* v_cls_3672_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v_fns_u2082_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v_fns_u2081_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; 
v_options_3669_ = lean_ctor_get(v_a_3428_, 2);
v_inheritedTraceOptions_3670_ = lean_ctor_get(v_a_3428_, 13);
v_hasTrace_3671_ = lean_ctor_get_uint8(v_options_3669_, sizeof(void*)*1);
v_cls_3672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3671_ == 0)
{
v___y_3791_ = v_a_3420_;
v___y_3792_ = v_a_3421_;
v___y_3793_ = v_a_3422_;
v___y_3794_ = v_a_3423_;
v___y_3795_ = v_a_3424_;
v___y_3796_ = v_a_3425_;
v___y_3797_ = v_a_3426_;
v___y_3798_ = v_a_3427_;
v___y_3799_ = v_a_3428_;
v___y_3800_ = v_a_3429_;
goto v___jp_3790_;
}
else
{
lean_object* v___x_3871_; uint8_t v___x_3872_; 
v___x_3871_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3872_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3670_, v_options_3669_, v___x_3871_);
if (v___x_3872_ == 0)
{
v___y_3791_ = v_a_3420_;
v___y_3792_ = v_a_3421_;
v___y_3793_ = v_a_3422_;
v___y_3794_ = v_a_3423_;
v___y_3795_ = v_a_3424_;
v___y_3796_ = v_a_3425_;
v___y_3797_ = v_a_3426_;
v___y_3798_ = v_a_3427_;
v___y_3799_ = v_a_3428_;
v___y_3800_ = v_a_3429_;
goto v___jp_3790_;
}
else
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Lean_Meta_Grind_updateLastTag(v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v___x_3874_; 
lean_dec_ref_known(v___x_3873_, 1);
lean_inc_ref(v_lhs_3413_);
v___x_3874_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3413_, v_a_3420_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3874_, 1);
lean_inc_ref(v_rhs_3414_);
v___x_3876_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3414_, v_a_3420_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v___x_3878_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
lean_ctor_set(v___x_3879_, 1, v_a_3875_);
v___x_3880_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v_a_3877_);
v___x_3883_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3672_, v___x_3882_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_dec_ref_known(v___x_3883_, 1);
v___y_3791_ = v_a_3420_;
v___y_3792_ = v_a_3421_;
v___y_3793_ = v_a_3422_;
v___y_3794_ = v_a_3423_;
v___y_3795_ = v_a_3424_;
v___y_3796_ = v_a_3425_;
v___y_3797_ = v_a_3426_;
v___y_3798_ = v_a_3427_;
v___y_3799_ = v_a_3428_;
v___y_3800_ = v_a_3429_;
goto v___jp_3790_;
}
else
{
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhsNode_3415_);
lean_dec_ref(v_rhs_3414_);
lean_dec_ref(v_lhs_3413_);
lean_dec_ref(v_proof_3411_);
return v___x_3883_;
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec(v_a_3875_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhsNode_3415_);
lean_dec_ref(v_rhs_3414_);
lean_dec_ref(v_lhs_3413_);
lean_dec_ref(v_proof_3411_);
v_a_3884_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3876_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3876_);
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
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhsNode_3415_);
lean_dec_ref(v_rhs_3414_);
lean_dec_ref(v_lhs_3413_);
lean_dec_ref(v_proof_3411_);
v_a_3892_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3874_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3874_);
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
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhsNode_3415_);
lean_dec_ref(v_rhs_3414_);
lean_dec_ref(v_lhs_3413_);
lean_dec_ref(v_proof_3411_);
return v___x_3873_;
}
}
}
v___jp_3431_:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3438_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3474_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3451_ = v___x_3448_;
v_isShared_3452_ = v_isSharedCheck_3474_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3448_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3474_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
uint8_t v___x_3453_; 
v___x_3453_ = lean_unbox(v_a_3449_);
lean_dec(v_a_3449_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_del_object(v___x_3451_);
v___x_3454_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3435_);
lean_dec(v___y_3435_);
v___x_3455_ = lean_box(0);
v___x_3456_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3454_, v___x_3455_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___x_3454_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v___x_3457_; 
lean_dec_ref_known(v___x_3456_, 1);
v___x_3457_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3432_, v___x_3455_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v___x_3458_; 
lean_dec_ref_known(v___x_3457_, 1);
v___x_3458_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3433_, v___y_3436_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec_ref(v___y_3436_);
lean_dec_ref(v___y_3433_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v___x_3459_; 
lean_dec_ref_known(v___x_3458_, 1);
v___x_3459_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3468_; 
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; 
v_unused_3469_ = lean_ctor_get(v___x_3459_, 0);
lean_dec(v_unused_3469_);
v___x_3461_ = v___x_3459_;
v_isShared_3462_ = v_isSharedCheck_3468_;
goto v_resetjp_3460_;
}
else
{
lean_dec(v___x_3459_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3468_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
uint8_t v___x_3463_; 
v___x_3463_ = l_Lean_Expr_isTrue(v___y_3434_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3465_; 
lean_dec(v___y_3432_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3455_);
v___x_3465_ = v___x_3461_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3455_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
else
{
lean_object* v___x_3467_; 
lean_del_object(v___x_3461_);
v___x_3467_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3432_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3432_);
return v___x_3467_;
}
}
}
else
{
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3432_);
return v___x_3459_;
}
}
else
{
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3432_);
return v___x_3458_;
}
}
else
{
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec_ref(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
return v___x_3457_;
}
}
else
{
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec_ref(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
return v___x_3456_;
}
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
v___x_3470_ = lean_box(0);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3470_);
v___x_3472_ = v___x_3451_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
v_a_3475_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3448_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3448_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
v___jp_3483_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
lean_inc_ref(v___y_3490_);
v___x_3520_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3520_, 0, v___y_3490_);
lean_ctor_set(v___x_3520_, 1, v___y_3514_);
lean_ctor_set(v___x_3520_, 2, v___y_3518_);
lean_ctor_set(v___x_3520_, 3, v___y_3496_);
lean_ctor_set(v___x_3520_, 4, v___y_3485_);
lean_ctor_set(v___x_3520_, 5, v___y_3484_);
lean_ctor_set(v___x_3520_, 6, v___y_3503_);
lean_ctor_set(v___x_3520_, 7, v___y_3495_);
lean_ctor_set(v___x_3520_, 8, v___y_3492_);
lean_ctor_set(v___x_3520_, 9, v___y_3491_);
lean_ctor_set(v___x_3520_, 10, v___y_3509_);
lean_ctor_set(v___x_3520_, 11, v___y_3486_);
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*12, v___y_3504_);
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*12 + 1, v___y_3500_);
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*12 + 2, v___y_3511_);
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*12 + 3, v___y_3489_);
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*12 + 4, v___y_3519_);
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*12 + 5, v___y_3510_);
lean_inc_ref(v___y_3498_);
v___x_3521_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3498_, v___x_3520_, v___y_3501_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3522_; 
lean_dec_ref_known(v___x_3521_, 1);
lean_inc_ref(v___y_3488_);
v___x_3522_ = l_Lean_Meta_Grind_propagateBeta(v___y_3488_, v___y_3487_, v___y_3501_, v___y_3505_, v___y_3517_, v___y_3497_, v___y_3516_, v___y_3515_, v___y_3502_, v___y_3494_, v___y_3513_, v___y_3508_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v___x_3523_; 
lean_dec_ref_known(v___x_3522_, 1);
lean_inc_ref(v___y_3499_);
v___x_3523_ = l_Lean_Meta_Grind_propagateBeta(v___y_3499_, v___y_3506_, v___y_3501_, v___y_3505_, v___y_3517_, v___y_3497_, v___y_3516_, v___y_3515_, v___y_3502_, v___y_3494_, v___y_3513_, v___y_3508_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v___x_3524_; 
lean_dec_ref_known(v___x_3523_, 1);
v___x_3524_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3418_, v_lhsRoot_3417_, v___y_3501_, v___y_3502_, v___y_3494_, v___y_3513_, v___y_3508_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3526_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
v___x_3526_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3493_, v___y_3501_);
lean_dec_ref(v___y_3493_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v___x_3527_; 
lean_dec_ref_known(v___x_3526_, 1);
lean_inc_ref(v___y_3498_);
v___x_3527_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3507_, v___y_3498_, v___y_3501_, v___y_3505_, v___y_3517_, v___y_3497_, v___y_3516_, v___y_3515_, v___y_3502_, v___y_3494_, v___y_3513_, v___y_3508_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v___x_3528_; 
lean_dec_ref_known(v___x_3527_, 1);
v___x_3528_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3501_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; uint8_t v___x_3530_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v___x_3530_ = lean_unbox(v_a_3529_);
lean_dec(v_a_3529_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; 
v___x_3531_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3490_, v___y_3501_, v___y_3505_, v___y_3517_, v___y_3497_, v___y_3516_, v___y_3515_, v___y_3502_, v___y_3494_, v___y_3513_, v___y_3508_);
lean_dec_ref(v___y_3490_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_dec_ref_known(v___x_3531_, 1);
v___y_3432_ = v___y_3512_;
v___y_3433_ = v___y_3488_;
v___y_3434_ = v___y_3498_;
v___y_3435_ = v___y_3507_;
v___y_3436_ = v___y_3499_;
v___y_3437_ = v_a_3525_;
v___y_3438_ = v___y_3501_;
v___y_3439_ = v___y_3505_;
v___y_3440_ = v___y_3517_;
v___y_3441_ = v___y_3497_;
v___y_3442_ = v___y_3516_;
v___y_3443_ = v___y_3515_;
v___y_3444_ = v___y_3502_;
v___y_3445_ = v___y_3494_;
v___y_3446_ = v___y_3513_;
v___y_3447_ = v___y_3508_;
goto v___jp_3431_;
}
else
{
lean_dec(v_a_3525_);
lean_dec(v___y_3512_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v___y_3488_);
return v___x_3531_;
}
}
else
{
lean_dec_ref(v___y_3490_);
v___y_3432_ = v___y_3512_;
v___y_3433_ = v___y_3488_;
v___y_3434_ = v___y_3498_;
v___y_3435_ = v___y_3507_;
v___y_3436_ = v___y_3499_;
v___y_3437_ = v_a_3525_;
v___y_3438_ = v___y_3501_;
v___y_3439_ = v___y_3505_;
v___y_3440_ = v___y_3517_;
v___y_3441_ = v___y_3497_;
v___y_3442_ = v___y_3516_;
v___y_3443_ = v___y_3515_;
v___y_3444_ = v___y_3502_;
v___y_3445_ = v___y_3494_;
v___y_3446_ = v___y_3513_;
v___y_3447_ = v___y_3508_;
goto v___jp_3431_;
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec(v_a_3525_);
lean_dec(v___y_3512_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3488_);
v_a_3532_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3528_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3528_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_dec(v_a_3525_);
lean_dec(v___y_3512_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3488_);
return v___x_3527_;
}
}
else
{
lean_dec(v_a_3525_);
lean_dec(v___y_3512_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3488_);
return v___x_3526_;
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec(v___y_3512_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v___y_3493_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3488_);
v_a_3540_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3524_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3524_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_dec(v___y_3512_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v___y_3493_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3488_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
return v___x_3523_;
}
}
else
{
lean_dec(v___y_3512_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v___y_3493_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3488_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
return v___x_3522_;
}
}
else
{
lean_dec(v___y_3512_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v___y_3493_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
return v___x_3521_;
}
}
v___jp_3548_:
{
if (v_isHEq_3412_ == 0)
{
if (v___y_3550_ == 0)
{
v___y_3484_ = v___y_3549_;
v___y_3485_ = v___y_3553_;
v___y_3486_ = v___y_3552_;
v___y_3487_ = v___y_3551_;
v___y_3488_ = v___y_3554_;
v___y_3489_ = v___y_3585_;
v___y_3490_ = v___y_3555_;
v___y_3491_ = v___y_3556_;
v___y_3492_ = v___y_3557_;
v___y_3493_ = v___y_3558_;
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3562_;
v___y_3497_ = v___y_3561_;
v___y_3498_ = v___y_3563_;
v___y_3499_ = v___y_3564_;
v___y_3500_ = v___y_3565_;
v___y_3501_ = v___y_3566_;
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3568_;
v___y_3504_ = v___y_3569_;
v___y_3505_ = v___y_3570_;
v___y_3506_ = v___y_3571_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3573_;
v___y_3509_ = v___y_3574_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3577_;
v___y_3512_ = v___y_3578_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3579_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3576_;
goto v___jp_3483_;
}
else
{
v___y_3484_ = v___y_3549_;
v___y_3485_ = v___y_3553_;
v___y_3486_ = v___y_3552_;
v___y_3487_ = v___y_3551_;
v___y_3488_ = v___y_3554_;
v___y_3489_ = v___y_3585_;
v___y_3490_ = v___y_3555_;
v___y_3491_ = v___y_3556_;
v___y_3492_ = v___y_3557_;
v___y_3493_ = v___y_3558_;
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3562_;
v___y_3497_ = v___y_3561_;
v___y_3498_ = v___y_3563_;
v___y_3499_ = v___y_3564_;
v___y_3500_ = v___y_3565_;
v___y_3501_ = v___y_3566_;
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3568_;
v___y_3504_ = v___y_3569_;
v___y_3505_ = v___y_3570_;
v___y_3506_ = v___y_3571_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3573_;
v___y_3509_ = v___y_3574_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3577_;
v___y_3512_ = v___y_3578_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3579_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3550_;
goto v___jp_3483_;
}
}
else
{
v___y_3484_ = v___y_3549_;
v___y_3485_ = v___y_3553_;
v___y_3486_ = v___y_3552_;
v___y_3487_ = v___y_3551_;
v___y_3488_ = v___y_3554_;
v___y_3489_ = v___y_3585_;
v___y_3490_ = v___y_3555_;
v___y_3491_ = v___y_3556_;
v___y_3492_ = v___y_3557_;
v___y_3493_ = v___y_3558_;
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3562_;
v___y_3497_ = v___y_3561_;
v___y_3498_ = v___y_3563_;
v___y_3499_ = v___y_3564_;
v___y_3500_ = v___y_3565_;
v___y_3501_ = v___y_3566_;
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3568_;
v___y_3504_ = v___y_3569_;
v___y_3505_ = v___y_3570_;
v___y_3506_ = v___y_3571_;
v___y_3507_ = v___y_3572_;
v___y_3508_ = v___y_3573_;
v___y_3509_ = v___y_3574_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3577_;
v___y_3512_ = v___y_3578_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3579_;
v___y_3515_ = v___y_3581_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v_isHEq_3412_;
goto v___jp_3483_;
}
}
v___jp_3586_:
{
lean_object* v___x_3609_; 
v___x_3609_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3595_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
lean_dec_ref_known(v___x_3609_, 1);
v___x_3610_ = lean_st_ref_get(v___y_3599_);
v___x_3611_ = lean_st_ref_get(v___y_3599_);
lean_inc_ref(v___y_3598_);
v___x_3612_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3611_, v___y_3598_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___x_3611_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v_self_3614_; lean_object* v_root_3615_; lean_object* v_congr_3616_; lean_object* v_target_x3f_3617_; lean_object* v_proof_x3f_3618_; uint8_t v_flipped_3619_; lean_object* v_size_3620_; uint8_t v_interpreted_3621_; uint8_t v_ctor_3622_; uint8_t v_hasLambdas_3623_; uint8_t v_heqProofs_3624_; lean_object* v_idx_3625_; lean_object* v_generation_3626_; lean_object* v_mt_3627_; lean_object* v_sTerms_3628_; uint8_t v_funCC_3629_; lean_object* v_ematchDiagSource_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3659_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
v_self_3614_ = lean_ctor_get(v_a_3613_, 0);
v_root_3615_ = lean_ctor_get(v_a_3613_, 2);
v_congr_3616_ = lean_ctor_get(v_a_3613_, 3);
v_target_x3f_3617_ = lean_ctor_get(v_a_3613_, 4);
v_proof_x3f_3618_ = lean_ctor_get(v_a_3613_, 5);
v_flipped_3619_ = lean_ctor_get_uint8(v_a_3613_, sizeof(void*)*12);
v_size_3620_ = lean_ctor_get(v_a_3613_, 6);
v_interpreted_3621_ = lean_ctor_get_uint8(v_a_3613_, sizeof(void*)*12 + 1);
v_ctor_3622_ = lean_ctor_get_uint8(v_a_3613_, sizeof(void*)*12 + 2);
v_hasLambdas_3623_ = lean_ctor_get_uint8(v_a_3613_, sizeof(void*)*12 + 3);
v_heqProofs_3624_ = lean_ctor_get_uint8(v_a_3613_, sizeof(void*)*12 + 4);
v_idx_3625_ = lean_ctor_get(v_a_3613_, 7);
v_generation_3626_ = lean_ctor_get(v_a_3613_, 8);
v_mt_3627_ = lean_ctor_get(v_a_3613_, 9);
v_sTerms_3628_ = lean_ctor_get(v_a_3613_, 10);
v_funCC_3629_ = lean_ctor_get_uint8(v_a_3613_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3630_ = lean_ctor_get(v_a_3613_, 11);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_a_3613_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v_a_3613_, 1);
lean_dec(v_unused_3660_);
v___x_3632_ = v_a_3613_;
v_isShared_3633_ = v_isSharedCheck_3659_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_ematchDiagSource_3630_);
lean_inc(v_sTerms_3628_);
lean_inc(v_mt_3627_);
lean_inc(v_generation_3626_);
lean_inc(v_idx_3625_);
lean_inc(v_size_3620_);
lean_inc(v_proof_x3f_3618_);
lean_inc(v_target_x3f_3617_);
lean_inc(v_congr_3616_);
lean_inc(v_root_3615_);
lean_inc(v_self_3614_);
lean_dec(v_a_3613_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3659_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v_self_3634_; lean_object* v_next_3635_; lean_object* v_root_3636_; lean_object* v_congr_3637_; lean_object* v_target_x3f_3638_; lean_object* v_proof_x3f_3639_; uint8_t v_flipped_3640_; lean_object* v_size_3641_; uint8_t v_interpreted_3642_; uint8_t v_ctor_3643_; uint8_t v_hasLambdas_3644_; uint8_t v_heqProofs_3645_; lean_object* v_idx_3646_; lean_object* v_generation_3647_; lean_object* v_mt_3648_; lean_object* v_sTerms_3649_; uint8_t v_funCC_3650_; lean_object* v_ematchDiagSource_3651_; lean_object* v___x_3653_; 
v_self_3634_ = lean_ctor_get(v_rhsRoot_3418_, 0);
v_next_3635_ = lean_ctor_get(v_rhsRoot_3418_, 1);
v_root_3636_ = lean_ctor_get(v_rhsRoot_3418_, 2);
v_congr_3637_ = lean_ctor_get(v_rhsRoot_3418_, 3);
v_target_x3f_3638_ = lean_ctor_get(v_rhsRoot_3418_, 4);
v_proof_x3f_3639_ = lean_ctor_get(v_rhsRoot_3418_, 5);
v_flipped_3640_ = lean_ctor_get_uint8(v_rhsRoot_3418_, sizeof(void*)*12);
v_size_3641_ = lean_ctor_get(v_rhsRoot_3418_, 6);
v_interpreted_3642_ = lean_ctor_get_uint8(v_rhsRoot_3418_, sizeof(void*)*12 + 1);
v_ctor_3643_ = lean_ctor_get_uint8(v_rhsRoot_3418_, sizeof(void*)*12 + 2);
v_hasLambdas_3644_ = lean_ctor_get_uint8(v_rhsRoot_3418_, sizeof(void*)*12 + 3);
v_heqProofs_3645_ = lean_ctor_get_uint8(v_rhsRoot_3418_, sizeof(void*)*12 + 4);
v_idx_3646_ = lean_ctor_get(v_rhsRoot_3418_, 7);
v_generation_3647_ = lean_ctor_get(v_rhsRoot_3418_, 8);
v_mt_3648_ = lean_ctor_get(v_rhsRoot_3418_, 9);
v_sTerms_3649_ = lean_ctor_get(v_rhsRoot_3418_, 10);
v_funCC_3650_ = lean_ctor_get_uint8(v_rhsRoot_3418_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3651_ = lean_ctor_get(v_rhsRoot_3418_, 11);
lean_inc_ref(v_next_3635_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 1, v_next_3635_);
v___x_3653_ = v___x_3632_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_self_3614_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_next_3635_);
lean_ctor_set(v_reuseFailAlloc_3658_, 2, v_root_3615_);
lean_ctor_set(v_reuseFailAlloc_3658_, 3, v_congr_3616_);
lean_ctor_set(v_reuseFailAlloc_3658_, 4, v_target_x3f_3617_);
lean_ctor_set(v_reuseFailAlloc_3658_, 5, v_proof_x3f_3618_);
lean_ctor_set(v_reuseFailAlloc_3658_, 6, v_size_3620_);
lean_ctor_set(v_reuseFailAlloc_3658_, 7, v_idx_3625_);
lean_ctor_set(v_reuseFailAlloc_3658_, 8, v_generation_3626_);
lean_ctor_set(v_reuseFailAlloc_3658_, 9, v_mt_3627_);
lean_ctor_set(v_reuseFailAlloc_3658_, 10, v_sTerms_3628_);
lean_ctor_set(v_reuseFailAlloc_3658_, 11, v_ematchDiagSource_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*12, v_flipped_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*12 + 1, v_interpreted_3621_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*12 + 2, v_ctor_3622_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*12 + 3, v_hasLambdas_3623_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*12 + 4, v_heqProofs_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3658_, sizeof(void*)*12 + 5, v_funCC_3629_);
v___x_3653_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3597_, v___x_3653_, v___y_3599_);
if (lean_obj_tag(v___x_3654_) == 0)
{
uint8_t v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
lean_dec_ref_known(v___x_3654_, 1);
v___x_3655_ = 0;
v___x_3656_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3610_, v_lhs_3413_, v___x_3655_);
lean_dec(v___x_3610_);
v___x_3657_ = lean_nat_add(v_size_3641_, v___y_3588_);
lean_dec(v___y_3588_);
if (v_hasLambdas_3644_ == 0)
{
lean_inc_ref(v_root_3636_);
lean_inc(v_sTerms_3649_);
lean_inc_ref(v_congr_3637_);
lean_inc(v_idx_3646_);
lean_inc(v_generation_3647_);
lean_inc(v_mt_3648_);
lean_inc_ref(v_self_3634_);
lean_inc(v_target_x3f_3638_);
lean_inc(v_ematchDiagSource_3651_);
lean_inc(v_proof_x3f_3639_);
v___y_3549_ = v_proof_x3f_3639_;
v___y_3550_ = v_heqProofs_3645_;
v___y_3551_ = v___y_3591_;
v___y_3552_ = v_ematchDiagSource_3651_;
v___y_3553_ = v_target_x3f_3638_;
v___y_3554_ = v___y_3593_;
v___y_3555_ = v_self_3634_;
v___y_3556_ = v_mt_3648_;
v___y_3557_ = v_generation_3647_;
v___y_3558_ = v___y_3598_;
v___y_3559_ = v___y_3606_;
v___y_3560_ = v_idx_3646_;
v___y_3561_ = v___y_3602_;
v___y_3562_ = v_congr_3637_;
v___y_3563_ = v___y_3594_;
v___y_3564_ = v___y_3596_;
v___y_3565_ = v_interpreted_3642_;
v___y_3566_ = v___y_3599_;
v___y_3567_ = v___y_3605_;
v___y_3568_ = v___x_3657_;
v___y_3569_ = v_flipped_3640_;
v___y_3570_ = v___y_3600_;
v___y_3571_ = v___y_3592_;
v___y_3572_ = v___y_3595_;
v___y_3573_ = v___y_3608_;
v___y_3574_ = v_sTerms_3649_;
v___y_3575_ = v_funCC_3650_;
v___y_3576_ = v___y_3587_;
v___y_3577_ = v_ctor_3643_;
v___y_3578_ = v___x_3656_;
v___y_3579_ = v___y_3590_;
v___y_3580_ = v___y_3607_;
v___y_3581_ = v___y_3604_;
v___y_3582_ = v___y_3603_;
v___y_3583_ = v___y_3601_;
v___y_3584_ = v_root_3636_;
v___y_3585_ = v___y_3589_;
goto v___jp_3548_;
}
else
{
lean_inc_ref(v_root_3636_);
lean_inc(v_sTerms_3649_);
lean_inc_ref(v_congr_3637_);
lean_inc(v_idx_3646_);
lean_inc(v_generation_3647_);
lean_inc(v_mt_3648_);
lean_inc_ref(v_self_3634_);
lean_inc(v_target_x3f_3638_);
lean_inc(v_ematchDiagSource_3651_);
lean_inc(v_proof_x3f_3639_);
v___y_3549_ = v_proof_x3f_3639_;
v___y_3550_ = v_heqProofs_3645_;
v___y_3551_ = v___y_3591_;
v___y_3552_ = v_ematchDiagSource_3651_;
v___y_3553_ = v_target_x3f_3638_;
v___y_3554_ = v___y_3593_;
v___y_3555_ = v_self_3634_;
v___y_3556_ = v_mt_3648_;
v___y_3557_ = v_generation_3647_;
v___y_3558_ = v___y_3598_;
v___y_3559_ = v___y_3606_;
v___y_3560_ = v_idx_3646_;
v___y_3561_ = v___y_3602_;
v___y_3562_ = v_congr_3637_;
v___y_3563_ = v___y_3594_;
v___y_3564_ = v___y_3596_;
v___y_3565_ = v_interpreted_3642_;
v___y_3566_ = v___y_3599_;
v___y_3567_ = v___y_3605_;
v___y_3568_ = v___x_3657_;
v___y_3569_ = v_flipped_3640_;
v___y_3570_ = v___y_3600_;
v___y_3571_ = v___y_3592_;
v___y_3572_ = v___y_3595_;
v___y_3573_ = v___y_3608_;
v___y_3574_ = v_sTerms_3649_;
v___y_3575_ = v_funCC_3650_;
v___y_3576_ = v___y_3587_;
v___y_3577_ = v_ctor_3643_;
v___y_3578_ = v___x_3656_;
v___y_3579_ = v___y_3590_;
v___y_3580_ = v___y_3607_;
v___y_3581_ = v___y_3604_;
v___y_3582_ = v___y_3603_;
v___y_3583_ = v___y_3601_;
v___y_3584_ = v_root_3636_;
v___y_3585_ = v_hasLambdas_3644_;
goto v___jp_3548_;
}
}
else
{
lean_dec(v___x_3610_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3588_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_lhs_3413_);
return v___x_3654_;
}
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec(v___x_3610_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3588_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_lhs_3413_);
v_a_3661_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3612_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3612_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
else
{
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3588_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_lhs_3413_);
return v___x_3609_;
}
}
v___jp_3673_:
{
lean_object* v_self_3689_; lean_object* v_next_3690_; lean_object* v_size_3691_; uint8_t v_hasLambdas_3692_; uint8_t v_heqProofs_3693_; lean_object* v___x_3694_; 
v_self_3689_ = lean_ctor_get(v_lhsRoot_3417_, 0);
v_next_3690_ = lean_ctor_get(v_lhsRoot_3417_, 1);
v_size_3691_ = lean_ctor_get(v_lhsRoot_3417_, 6);
v_hasLambdas_3692_ = lean_ctor_get_uint8(v_lhsRoot_3417_, sizeof(void*)*12 + 3);
v_heqProofs_3693_ = lean_ctor_get_uint8(v_lhsRoot_3417_, sizeof(void*)*12 + 4);
v___x_3694_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3689_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v_root_3696_; lean_object* v___x_3697_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
v_root_3696_ = lean_ctor_get(v_rhsNode_3416_, 2);
lean_inc_ref_n(v_root_3696_, 2);
lean_dec_ref(v_rhsNode_3416_);
lean_inc_ref(v_lhs_3413_);
v___x_3697_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3413_, v_root_3696_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_options_3698_; uint8_t v_hasTrace_3699_; 
lean_dec_ref_known(v___x_3697_, 1);
v_options_3698_ = lean_ctor_get(v___y_3687_, 2);
v_hasTrace_3699_ = lean_ctor_get_uint8(v_options_3698_, sizeof(void*)*1);
if (v_hasTrace_3699_ == 0)
{
lean_inc_ref(v_self_3689_);
lean_inc_ref(v_next_3690_);
lean_inc(v_size_3691_);
v___y_3587_ = v_heqProofs_3693_;
v___y_3588_ = v_size_3691_;
v___y_3589_ = v_hasLambdas_3692_;
v___y_3590_ = v_next_3690_;
v___y_3591_ = v___y_3674_;
v___y_3592_ = v_fns_u2082_3678_;
v___y_3593_ = v___y_3675_;
v___y_3594_ = v_root_3696_;
v___y_3595_ = v_a_3695_;
v___y_3596_ = v___y_3676_;
v___y_3597_ = v___y_3677_;
v___y_3598_ = v_self_3689_;
v___y_3599_ = v___y_3679_;
v___y_3600_ = v___y_3680_;
v___y_3601_ = v___y_3681_;
v___y_3602_ = v___y_3682_;
v___y_3603_ = v___y_3683_;
v___y_3604_ = v___y_3684_;
v___y_3605_ = v___y_3685_;
v___y_3606_ = v___y_3686_;
v___y_3607_ = v___y_3687_;
v___y_3608_ = v___y_3688_;
goto v___jp_3586_;
}
else
{
lean_object* v_inheritedTraceOptions_3700_; lean_object* v___x_3701_; uint8_t v___x_3702_; 
v_inheritedTraceOptions_3700_ = lean_ctor_get(v___y_3687_, 13);
v___x_3701_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3702_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3700_, v_options_3698_, v___x_3701_);
if (v___x_3702_ == 0)
{
lean_inc_ref(v_self_3689_);
lean_inc_ref(v_next_3690_);
lean_inc(v_size_3691_);
v___y_3587_ = v_heqProofs_3693_;
v___y_3588_ = v_size_3691_;
v___y_3589_ = v_hasLambdas_3692_;
v___y_3590_ = v_next_3690_;
v___y_3591_ = v___y_3674_;
v___y_3592_ = v_fns_u2082_3678_;
v___y_3593_ = v___y_3675_;
v___y_3594_ = v_root_3696_;
v___y_3595_ = v_a_3695_;
v___y_3596_ = v___y_3676_;
v___y_3597_ = v___y_3677_;
v___y_3598_ = v_self_3689_;
v___y_3599_ = v___y_3679_;
v___y_3600_ = v___y_3680_;
v___y_3601_ = v___y_3681_;
v___y_3602_ = v___y_3682_;
v___y_3603_ = v___y_3683_;
v___y_3604_ = v___y_3684_;
v___y_3605_ = v___y_3685_;
v___y_3606_ = v___y_3686_;
v___y_3607_ = v___y_3687_;
v___y_3608_ = v___y_3688_;
goto v___jp_3586_;
}
else
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_Meta_Grind_updateLastTag(v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v___x_3704_; 
lean_dec_ref_known(v___x_3703_, 1);
lean_inc_ref(v_lhs_3413_);
v___x_3704_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3413_, v___y_3679_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3706_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
lean_inc_ref(v_root_3696_);
v___x_3706_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3696_, v___y_3679_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v___x_3708_ = lean_st_ref_get(v___y_3679_);
lean_inc_ref(v_lhs_3413_);
v___x_3709_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3708_, v_lhs_3413_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___x_3708_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3711_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___x_3709_, 1);
v___x_3711_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3710_, v___y_3679_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v___x_3713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v_a_3705_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
lean_ctor_set(v___x_3715_, 1, v_a_3707_);
v___x_3716_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
lean_ctor_set(v___x_3718_, 1, v_a_3712_);
v___x_3719_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3672_, v___x_3718_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_dec_ref_known(v___x_3719_, 1);
lean_inc_ref(v_self_3689_);
lean_inc_ref(v_next_3690_);
lean_inc(v_size_3691_);
v___y_3587_ = v_heqProofs_3693_;
v___y_3588_ = v_size_3691_;
v___y_3589_ = v_hasLambdas_3692_;
v___y_3590_ = v_next_3690_;
v___y_3591_ = v___y_3674_;
v___y_3592_ = v_fns_u2082_3678_;
v___y_3593_ = v___y_3675_;
v___y_3594_ = v_root_3696_;
v___y_3595_ = v_a_3695_;
v___y_3596_ = v___y_3676_;
v___y_3597_ = v___y_3677_;
v___y_3598_ = v_self_3689_;
v___y_3599_ = v___y_3679_;
v___y_3600_ = v___y_3680_;
v___y_3601_ = v___y_3681_;
v___y_3602_ = v___y_3682_;
v___y_3603_ = v___y_3683_;
v___y_3604_ = v___y_3684_;
v___y_3605_ = v___y_3685_;
v___y_3606_ = v___y_3686_;
v___y_3607_ = v___y_3687_;
v___y_3608_ = v___y_3688_;
goto v___jp_3586_;
}
else
{
lean_dec_ref(v_root_3696_);
lean_dec(v_a_3695_);
lean_dec_ref(v_fns_u2082_3678_);
lean_dec_ref(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_lhs_3413_);
return v___x_3719_;
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec(v_a_3707_);
lean_dec(v_a_3705_);
lean_dec_ref(v_root_3696_);
lean_dec(v_a_3695_);
lean_dec_ref(v_fns_u2082_3678_);
lean_dec_ref(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_lhs_3413_);
v_a_3720_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3711_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3711_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec(v_a_3707_);
lean_dec(v_a_3705_);
lean_dec_ref(v_root_3696_);
lean_dec(v_a_3695_);
lean_dec_ref(v_fns_u2082_3678_);
lean_dec_ref(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_lhs_3413_);
v_a_3728_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3709_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3709_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v_a_3705_);
lean_dec_ref(v_root_3696_);
lean_dec(v_a_3695_);
lean_dec_ref(v_fns_u2082_3678_);
lean_dec_ref(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_lhs_3413_);
v_a_3736_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3706_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3706_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec_ref(v_root_3696_);
lean_dec(v_a_3695_);
lean_dec_ref(v_fns_u2082_3678_);
lean_dec_ref(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_lhs_3413_);
v_a_3744_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3704_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3704_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
lean_dec_ref(v_root_3696_);
lean_dec(v_a_3695_);
lean_dec_ref(v_fns_u2082_3678_);
lean_dec_ref(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_lhs_3413_);
return v___x_3703_;
}
}
}
}
else
{
lean_dec_ref(v_root_3696_);
lean_dec(v_a_3695_);
lean_dec_ref(v_fns_u2082_3678_);
lean_dec_ref(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_lhs_3413_);
return v___x_3697_;
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec_ref(v_fns_u2082_3678_);
lean_dec_ref(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhs_3413_);
v_a_3752_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3694_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3694_);
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
v___jp_3760_:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3775_ = lean_array_get_size(v___y_3762_);
v___x_3776_ = lean_unsigned_to_nat(0u);
v___x_3777_ = lean_nat_dec_eq(v___x_3775_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v_self_3778_; lean_object* v___x_3779_; 
v_self_3778_ = lean_ctor_get(v_lhsRoot_3417_, 0);
lean_inc_ref(v_self_3778_);
v___x_3779_ = l_Lean_Meta_Grind_getFnRoots(v_self_3778_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___y_3674_ = v_fns_u2081_3764_;
v___y_3675_ = v___y_3761_;
v___y_3676_ = v___y_3762_;
v___y_3677_ = v___y_3763_;
v_fns_u2082_3678_ = v_a_3780_;
v___y_3679_ = v___y_3765_;
v___y_3680_ = v___y_3766_;
v___y_3681_ = v___y_3767_;
v___y_3682_ = v___y_3768_;
v___y_3683_ = v___y_3769_;
v___y_3684_ = v___y_3770_;
v___y_3685_ = v___y_3771_;
v___y_3686_ = v___y_3772_;
v___y_3687_ = v___y_3773_;
v___y_3688_ = v___y_3774_;
goto v___jp_3673_;
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec_ref(v_fns_u2081_3764_);
lean_dec_ref(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhs_3413_);
v_a_3781_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3779_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3779_);
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
lean_object* v___x_3789_; 
v___x_3789_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3674_ = v_fns_u2081_3764_;
v___y_3675_ = v___y_3761_;
v___y_3676_ = v___y_3762_;
v___y_3677_ = v___y_3763_;
v_fns_u2082_3678_ = v___x_3789_;
v___y_3679_ = v___y_3765_;
v___y_3680_ = v___y_3766_;
v___y_3681_ = v___y_3767_;
v___y_3682_ = v___y_3768_;
v___y_3683_ = v___y_3769_;
v___y_3684_ = v___y_3770_;
v___y_3685_ = v___y_3771_;
v___y_3686_ = v___y_3772_;
v___y_3687_ = v___y_3773_;
v___y_3688_ = v___y_3774_;
goto v___jp_3673_;
}
}
v___jp_3790_:
{
lean_object* v___x_3801_; 
lean_inc_ref(v_lhs_3413_);
v___x_3801_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3413_, v___y_3791_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3869_; 
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3869_ == 0)
{
lean_object* v_unused_3870_; 
v_unused_3870_ = lean_ctor_get(v___x_3801_, 0);
lean_dec(v_unused_3870_);
v___x_3803_ = v___x_3801_;
v_isShared_3804_ = v_isSharedCheck_3869_;
goto v_resetjp_3802_;
}
else
{
lean_dec(v___x_3801_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3869_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v_self_3805_; lean_object* v_next_3806_; lean_object* v_root_3807_; lean_object* v_congr_3808_; lean_object* v_size_3809_; uint8_t v_interpreted_3810_; uint8_t v_ctor_3811_; uint8_t v_hasLambdas_3812_; uint8_t v_heqProofs_3813_; lean_object* v_idx_3814_; lean_object* v_generation_3815_; lean_object* v_mt_3816_; lean_object* v_sTerms_3817_; uint8_t v_funCC_3818_; lean_object* v_ematchDiagSource_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3866_; 
v_self_3805_ = lean_ctor_get(v_lhsNode_3415_, 0);
v_next_3806_ = lean_ctor_get(v_lhsNode_3415_, 1);
v_root_3807_ = lean_ctor_get(v_lhsNode_3415_, 2);
v_congr_3808_ = lean_ctor_get(v_lhsNode_3415_, 3);
v_size_3809_ = lean_ctor_get(v_lhsNode_3415_, 6);
v_interpreted_3810_ = lean_ctor_get_uint8(v_lhsNode_3415_, sizeof(void*)*12 + 1);
v_ctor_3811_ = lean_ctor_get_uint8(v_lhsNode_3415_, sizeof(void*)*12 + 2);
v_hasLambdas_3812_ = lean_ctor_get_uint8(v_lhsNode_3415_, sizeof(void*)*12 + 3);
v_heqProofs_3813_ = lean_ctor_get_uint8(v_lhsNode_3415_, sizeof(void*)*12 + 4);
v_idx_3814_ = lean_ctor_get(v_lhsNode_3415_, 7);
v_generation_3815_ = lean_ctor_get(v_lhsNode_3415_, 8);
v_mt_3816_ = lean_ctor_get(v_lhsNode_3415_, 9);
v_sTerms_3817_ = lean_ctor_get(v_lhsNode_3415_, 10);
v_funCC_3818_ = lean_ctor_get_uint8(v_lhsNode_3415_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3819_ = lean_ctor_get(v_lhsNode_3415_, 11);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_lhsNode_3415_);
if (v_isSharedCheck_3866_ == 0)
{
lean_object* v_unused_3867_; lean_object* v_unused_3868_; 
v_unused_3867_ = lean_ctor_get(v_lhsNode_3415_, 5);
lean_dec(v_unused_3867_);
v_unused_3868_ = lean_ctor_get(v_lhsNode_3415_, 4);
lean_dec(v_unused_3868_);
v___x_3821_ = v_lhsNode_3415_;
v_isShared_3822_ = v_isSharedCheck_3866_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_ematchDiagSource_3819_);
lean_inc(v_sTerms_3817_);
lean_inc(v_mt_3816_);
lean_inc(v_generation_3815_);
lean_inc(v_idx_3814_);
lean_inc(v_size_3809_);
lean_inc(v_congr_3808_);
lean_inc(v_root_3807_);
lean_inc(v_next_3806_);
lean_inc(v_self_3805_);
lean_dec(v_lhsNode_3415_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3866_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 1);
lean_ctor_set(v___x_3803_, 0, v_rhs_3414_);
v___x_3824_ = v___x_3803_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_rhs_3414_);
v___x_3824_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
lean_object* v___x_3825_; lean_object* v___x_3827_; 
v___x_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3825_, 0, v_proof_3411_);
lean_inc_ref(v_root_3807_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 5, v___x_3825_);
lean_ctor_set(v___x_3821_, 4, v___x_3824_);
v___x_3827_ = v___x_3821_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_self_3805_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_next_3806_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v_root_3807_);
lean_ctor_set(v_reuseFailAlloc_3864_, 3, v_congr_3808_);
lean_ctor_set(v_reuseFailAlloc_3864_, 4, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3864_, 5, v___x_3825_);
lean_ctor_set(v_reuseFailAlloc_3864_, 6, v_size_3809_);
lean_ctor_set(v_reuseFailAlloc_3864_, 7, v_idx_3814_);
lean_ctor_set(v_reuseFailAlloc_3864_, 8, v_generation_3815_);
lean_ctor_set(v_reuseFailAlloc_3864_, 9, v_mt_3816_);
lean_ctor_set(v_reuseFailAlloc_3864_, 10, v_sTerms_3817_);
lean_ctor_set(v_reuseFailAlloc_3864_, 11, v_ematchDiagSource_3819_);
lean_ctor_set_uint8(v_reuseFailAlloc_3864_, sizeof(void*)*12 + 1, v_interpreted_3810_);
lean_ctor_set_uint8(v_reuseFailAlloc_3864_, sizeof(void*)*12 + 2, v_ctor_3811_);
lean_ctor_set_uint8(v_reuseFailAlloc_3864_, sizeof(void*)*12 + 3, v_hasLambdas_3812_);
lean_ctor_set_uint8(v_reuseFailAlloc_3864_, sizeof(void*)*12 + 4, v_heqProofs_3813_);
lean_ctor_set_uint8(v_reuseFailAlloc_3864_, sizeof(void*)*12 + 5, v_funCC_3818_);
v___x_3827_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3828_; 
lean_ctor_set_uint8(v___x_3827_, sizeof(void*)*12, v_flipped_3419_);
lean_inc_ref(v_lhs_3413_);
v___x_3828_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3413_, v___x_3827_, v___y_3791_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v___x_3829_; 
lean_dec_ref_known(v___x_3828_, 1);
v___x_3829_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3417_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3831_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref_known(v___x_3829_, 1);
v___x_3831_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3418_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_a_3832_);
lean_dec_ref_known(v___x_3831_, 1);
v___x_3833_ = lean_array_get_size(v_a_3830_);
v___x_3834_ = lean_unsigned_to_nat(0u);
v___x_3835_ = lean_nat_dec_eq(v___x_3833_, v___x_3834_);
if (v___x_3835_ == 0)
{
lean_object* v_self_3836_; lean_object* v___x_3837_; 
v_self_3836_ = lean_ctor_get(v_rhsRoot_3418_, 0);
lean_inc_ref(v_self_3836_);
v___x_3837_ = l_Lean_Meta_Grind_getFnRoots(v_self_3836_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3837_, 1);
v___y_3761_ = v_a_3830_;
v___y_3762_ = v_a_3832_;
v___y_3763_ = v_root_3807_;
v_fns_u2081_3764_ = v_a_3838_;
v___y_3765_ = v___y_3791_;
v___y_3766_ = v___y_3792_;
v___y_3767_ = v___y_3793_;
v___y_3768_ = v___y_3794_;
v___y_3769_ = v___y_3795_;
v___y_3770_ = v___y_3796_;
v___y_3771_ = v___y_3797_;
v___y_3772_ = v___y_3798_;
v___y_3773_ = v___y_3799_;
v___y_3774_ = v___y_3800_;
goto v___jp_3760_;
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_dec(v_a_3832_);
lean_dec(v_a_3830_);
lean_dec_ref(v_root_3807_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhs_3413_);
v_a_3839_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___x_3837_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3837_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
else
{
lean_object* v___x_3847_; 
v___x_3847_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3761_ = v_a_3830_;
v___y_3762_ = v_a_3832_;
v___y_3763_ = v_root_3807_;
v_fns_u2081_3764_ = v___x_3847_;
v___y_3765_ = v___y_3791_;
v___y_3766_ = v___y_3792_;
v___y_3767_ = v___y_3793_;
v___y_3768_ = v___y_3794_;
v___y_3769_ = v___y_3795_;
v___y_3770_ = v___y_3796_;
v___y_3771_ = v___y_3797_;
v___y_3772_ = v___y_3798_;
v___y_3773_ = v___y_3799_;
v___y_3774_ = v___y_3800_;
goto v___jp_3760_;
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_dec(v_a_3830_);
lean_dec_ref(v_root_3807_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhs_3413_);
v_a_3848_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3831_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3831_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec_ref(v_root_3807_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhs_3413_);
v_a_3856_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3829_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3829_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
else
{
lean_dec_ref(v_root_3807_);
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhs_3413_);
return v___x_3828_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3418_);
lean_dec_ref(v_lhsRoot_3417_);
lean_dec_ref(v_rhsNode_3416_);
lean_dec_ref(v_lhsNode_3415_);
lean_dec_ref(v_rhs_3414_);
lean_dec_ref(v_lhs_3413_);
lean_dec_ref(v_proof_3411_);
return v___x_3801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3900_ = _args[0];
lean_object* v_isHEq_3901_ = _args[1];
lean_object* v_lhs_3902_ = _args[2];
lean_object* v_rhs_3903_ = _args[3];
lean_object* v_lhsNode_3904_ = _args[4];
lean_object* v_rhsNode_3905_ = _args[5];
lean_object* v_lhsRoot_3906_ = _args[6];
lean_object* v_rhsRoot_3907_ = _args[7];
lean_object* v_flipped_3908_ = _args[8];
lean_object* v_a_3909_ = _args[9];
lean_object* v_a_3910_ = _args[10];
lean_object* v_a_3911_ = _args[11];
lean_object* v_a_3912_ = _args[12];
lean_object* v_a_3913_ = _args[13];
lean_object* v_a_3914_ = _args[14];
lean_object* v_a_3915_ = _args[15];
lean_object* v_a_3916_ = _args[16];
lean_object* v_a_3917_ = _args[17];
lean_object* v_a_3918_ = _args[18];
lean_object* v_a_3919_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3920_; uint8_t v_flipped_boxed_3921_; lean_object* v_res_3922_; 
v_isHEq_boxed_3920_ = lean_unbox(v_isHEq_3901_);
v_flipped_boxed_3921_ = lean_unbox(v_flipped_3908_);
v_res_3922_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3900_, v_isHEq_boxed_3920_, v_lhs_3902_, v_rhs_3903_, v_lhsNode_3904_, v_rhsNode_3905_, v_lhsRoot_3906_, v_rhsRoot_3907_, v_flipped_boxed_3921_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_);
lean_dec(v_a_3918_);
lean_dec_ref(v_a_3917_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec(v_a_3909_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3923_, lean_object* v_as_x27_3924_, lean_object* v_b_3925_, lean_object* v_a_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3924_, v_b_3925_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3939_, lean_object* v_as_x27_3940_, lean_object* v_b_3941_, lean_object* v_a_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3939_, v_as_x27_3940_, v_b_3941_, v_a_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v_as_x27_3940_);
lean_dec(v_as_3939_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3955_, lean_object* v_as_x27_3956_, lean_object* v_b_3957_, lean_object* v_a_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3956_, v_b_3957_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3971_, lean_object* v_as_x27_3972_, lean_object* v_b_3973_, lean_object* v_a_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3971_, v_as_x27_3972_, v_b_3973_, v_a_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec(v_as_x27_3972_);
lean_dec(v_as_3971_);
return v_res_3986_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_3989_ = l_Lean_stringToMessageData(v___x_3988_);
return v___x_3989_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_3995_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3996_ = l_Lean_Name_append(v___x_3995_, v___x_3994_);
return v___x_3996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_3999_ = l_Lean_stringToMessageData(v___x_3998_);
return v___x_3999_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4002_ = l_Lean_stringToMessageData(v___x_4001_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4003_, lean_object* v_rhs_4004_, lean_object* v_proof_4005_, uint8_t v_isHEq_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4021_ = lean_st_ref_get(v_a_4007_);
lean_inc_ref(v_lhs_4003_);
v___x_4022_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4021_, v_lhs_4003_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
lean_dec(v___x_4021_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v___x_4022_, 1);
v___x_4024_ = lean_st_ref_get(v_a_4007_);
lean_inc_ref(v_rhs_4004_);
v___x_4025_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4024_, v_rhs_4004_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
lean_dec(v___x_4024_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v_root_4027_; lean_object* v_root_4028_; uint8_t v___x_4029_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
v_root_4027_ = lean_ctor_get(v_a_4023_, 2);
v_root_4028_ = lean_ctor_get(v_a_4026_, 2);
v___x_4029_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_root_4027_, v_root_4028_);
if (v___x_4029_ == 0)
{
lean_object* v_options_4030_; lean_object* v_inheritedTraceOptions_4031_; uint8_t v_hasTrace_4032_; uint8_t v___x_4033_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4070_; lean_object* v___y_4071_; uint8_t v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; uint8_t v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; uint8_t v___y_4111_; lean_object* v___y_4116_; lean_object* v___y_4117_; uint8_t v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4143_; uint8_t v___y_4144_; uint8_t v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; uint8_t v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; uint8_t v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; uint8_t v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; uint8_t v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; uint8_t v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; uint8_t v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; uint8_t v___y_4205_; uint8_t v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v_size_4215_; uint8_t v___y_4216_; lean_object* v___y_4217_; lean_object* v_size_4218_; uint8_t v_interpreted_4219_; uint8_t v_ctor_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; uint8_t v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; uint8_t v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; uint8_t v___y_4241_; lean_object* v___y_4252_; lean_object* v___y_4253_; uint8_t v_interpreted_4254_; uint8_t v_valueInconsistency_4255_; uint8_t v_trueEqFalse_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4269_; lean_object* v___y_4270_; uint8_t v_valueInconsistency_4271_; uint8_t v_trueEqFalse_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; uint8_t v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; uint8_t v___y_4339_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; 
v_options_4030_ = lean_ctor_get(v_a_4015_, 2);
v_inheritedTraceOptions_4031_ = lean_ctor_get(v_a_4015_, 13);
v_hasTrace_4032_ = lean_ctor_get_uint8(v_options_4030_, sizeof(void*)*1);
v___x_4033_ = 1;
if (v_hasTrace_4032_ == 0)
{
v___y_4346_ = v_a_4007_;
v___y_4347_ = v_a_4008_;
v___y_4348_ = v_a_4009_;
v___y_4349_ = v_a_4010_;
v___y_4350_ = v_a_4011_;
v___y_4351_ = v_a_4012_;
v___y_4352_ = v_a_4013_;
v___y_4353_ = v_a_4014_;
v___y_4354_ = v_a_4015_;
v___y_4355_ = v_a_4016_;
goto v___jp_4345_;
}
else
{
lean_object* v___x_4381_; lean_object* v_____do__lift_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___x_4396_; uint8_t v___x_4397_; 
v___x_4381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4396_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4397_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4031_, v_options_4030_, v___x_4396_);
if (v___x_4397_ == 0)
{
v___y_4346_ = v_a_4007_;
v___y_4347_ = v_a_4008_;
v___y_4348_ = v_a_4009_;
v___y_4349_ = v_a_4010_;
v___y_4350_ = v_a_4011_;
v___y_4351_ = v_a_4012_;
v___y_4352_ = v_a_4013_;
v___y_4353_ = v_a_4014_;
v___y_4354_ = v_a_4015_;
v___y_4355_ = v_a_4016_;
goto v___jp_4345_;
}
else
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Lean_Meta_Grind_updateLastTag(v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_dec_ref_known(v___x_4398_, 1);
if (v_isHEq_4006_ == 0)
{
lean_object* v___x_4399_; 
lean_inc_ref(v_rhs_4004_);
lean_inc_ref(v_lhs_4003_);
v___x_4399_ = l_Lean_Meta_mkEq(v_lhs_4003_, v_rhs_4004_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref_known(v___x_4399_, 1);
v_____do__lift_4383_ = v_a_4400_;
v___y_4384_ = v_a_4007_;
v___y_4385_ = v_a_4008_;
v___y_4386_ = v_a_4009_;
v___y_4387_ = v_a_4010_;
v___y_4388_ = v_a_4011_;
v___y_4389_ = v_a_4012_;
v___y_4390_ = v_a_4013_;
v___y_4391_ = v_a_4014_;
v___y_4392_ = v_a_4015_;
v___y_4393_ = v_a_4016_;
goto v___jp_4382_;
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_a_4026_);
lean_dec(v_a_4023_);
lean_dec_ref(v_proof_4005_);
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
v_a_4401_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4399_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4399_);
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
else
{
lean_object* v___x_4409_; 
lean_inc_ref(v_rhs_4004_);
lean_inc_ref(v_lhs_4003_);
v___x_4409_ = l_Lean_Meta_mkHEq(v_lhs_4003_, v_rhs_4004_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v_____do__lift_4383_ = v_a_4410_;
v___y_4384_ = v_a_4007_;
v___y_4385_ = v_a_4008_;
v___y_4386_ = v_a_4009_;
v___y_4387_ = v_a_4010_;
v___y_4388_ = v_a_4011_;
v___y_4389_ = v_a_4012_;
v___y_4390_ = v_a_4013_;
v___y_4391_ = v_a_4014_;
v___y_4392_ = v_a_4015_;
v___y_4393_ = v_a_4016_;
goto v___jp_4382_;
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_a_4026_);
lean_dec(v_a_4023_);
lean_dec_ref(v_proof_4005_);
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
v_a_4411_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4409_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4409_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
else
{
lean_dec(v_a_4026_);
lean_dec(v_a_4023_);
lean_dec_ref(v_proof_4005_);
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
return v___x_4398_;
}
}
v___jp_4382_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4394_ = l_Lean_MessageData_ofExpr(v_____do__lift_4383_);
v___x_4395_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4381_, v___x_4394_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_dec_ref_known(v___x_4395_, 1);
v___y_4346_ = v___y_4384_;
v___y_4347_ = v___y_4385_;
v___y_4348_ = v___y_4386_;
v___y_4349_ = v___y_4387_;
v___y_4350_ = v___y_4388_;
v___y_4351_ = v___y_4389_;
v___y_4352_ = v___y_4390_;
v___y_4353_ = v___y_4391_;
v___y_4354_ = v___y_4392_;
v___y_4355_ = v___y_4393_;
goto v___jp_4345_;
}
else
{
lean_dec(v_a_4026_);
lean_dec(v_a_4023_);
lean_dec_ref(v_proof_4005_);
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
return v___x_4395_;
}
}
}
v___jp_4034_:
{
lean_object* v_options_4045_; uint8_t v_hasTrace_4046_; 
v_options_4045_ = lean_ctor_get(v___y_4043_, 2);
v_hasTrace_4046_ = lean_ctor_get_uint8(v_options_4045_, sizeof(void*)*1);
if (v_hasTrace_4046_ == 0)
{
lean_object* v___x_4047_; 
v___x_4047_ = l_Lean_Meta_Grind_checkInvariants(v___x_4029_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
return v___x_4047_;
}
else
{
lean_object* v_inheritedTraceOptions_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
v_inheritedTraceOptions_4048_ = lean_ctor_get(v___y_4043_, 13);
v___x_4049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4050_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4051_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4048_, v_options_4045_, v___x_4050_);
if (v___x_4051_ == 0)
{
lean_object* v___x_4052_; 
v___x_4052_ = l_Lean_Meta_Grind_checkInvariants(v___x_4029_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
return v___x_4052_;
}
else
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Lean_Meta_Grind_updateLastTag(v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
lean_dec_ref_known(v___x_4053_, 1);
v___x_4054_ = lean_st_ref_get(v___y_4035_);
v___x_4055_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4054_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___x_4054_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___x_4055_, 1);
v___x_4057_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
lean_ctor_set(v___x_4058_, 1, v_a_4056_);
v___x_4059_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4049_, v___x_4058_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v___x_4060_; 
lean_dec_ref_known(v___x_4059_, 1);
v___x_4060_ = l_Lean_Meta_Grind_checkInvariants(v___x_4029_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
return v___x_4060_;
}
else
{
return v___x_4059_;
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
v_a_4061_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4055_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4055_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
else
{
return v___x_4053_;
}
}
}
}
v___jp_4069_:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4073_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; uint8_t v___x_4085_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4083_, 1);
v___x_4085_ = lean_unbox(v_a_4084_);
lean_dec(v_a_4084_);
if (v___x_4085_ == 0)
{
if (v___y_4072_ == 0)
{
lean_dec_ref(v___y_4071_);
lean_dec_ref(v___y_4070_);
v___y_4035_ = v___y_4073_;
v___y_4036_ = v___y_4074_;
v___y_4037_ = v___y_4075_;
v___y_4038_ = v___y_4076_;
v___y_4039_ = v___y_4077_;
v___y_4040_ = v___y_4078_;
v___y_4041_ = v___y_4079_;
v___y_4042_ = v___y_4080_;
v___y_4043_ = v___y_4081_;
v___y_4044_ = v___y_4082_;
goto v___jp_4034_;
}
else
{
lean_object* v_self_4086_; lean_object* v_self_4087_; lean_object* v___x_4088_; 
v_self_4086_ = lean_ctor_get(v___y_4071_, 0);
lean_inc_ref(v_self_4086_);
lean_dec_ref(v___y_4071_);
v_self_4087_ = lean_ctor_get(v___y_4070_, 0);
lean_inc_ref(v_self_4087_);
lean_dec_ref(v___y_4070_);
v___x_4088_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4086_, v_self_4087_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_dec_ref_known(v___x_4088_, 1);
v___y_4035_ = v___y_4073_;
v___y_4036_ = v___y_4074_;
v___y_4037_ = v___y_4075_;
v___y_4038_ = v___y_4076_;
v___y_4039_ = v___y_4077_;
v___y_4040_ = v___y_4078_;
v___y_4041_ = v___y_4079_;
v___y_4042_ = v___y_4080_;
v___y_4043_ = v___y_4081_;
v___y_4044_ = v___y_4082_;
goto v___jp_4034_;
}
else
{
return v___x_4088_;
}
}
}
else
{
lean_dec_ref(v___y_4071_);
lean_dec_ref(v___y_4070_);
v___y_4035_ = v___y_4073_;
v___y_4036_ = v___y_4074_;
v___y_4037_ = v___y_4075_;
v___y_4038_ = v___y_4076_;
v___y_4039_ = v___y_4077_;
v___y_4040_ = v___y_4078_;
v___y_4041_ = v___y_4079_;
v___y_4042_ = v___y_4080_;
v___y_4043_ = v___y_4081_;
v___y_4044_ = v___y_4082_;
goto v___jp_4034_;
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec_ref(v___y_4071_);
lean_dec_ref(v___y_4070_);
v_a_4089_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4083_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4083_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
v___jp_4097_:
{
if (v___y_4111_ == 0)
{
v___y_4070_ = v___y_4107_;
v___y_4071_ = v___y_4105_;
v___y_4072_ = v___y_4103_;
v___y_4073_ = v___y_4098_;
v___y_4074_ = v___y_4100_;
v___y_4075_ = v___y_4106_;
v___y_4076_ = v___y_4109_;
v___y_4077_ = v___y_4102_;
v___y_4078_ = v___y_4099_;
v___y_4079_ = v___y_4101_;
v___y_4080_ = v___y_4104_;
v___y_4081_ = v___y_4108_;
v___y_4082_ = v___y_4110_;
goto v___jp_4069_;
}
else
{
lean_object* v_self_4112_; lean_object* v_self_4113_; lean_object* v___x_4114_; 
v_self_4112_ = lean_ctor_get(v___y_4105_, 0);
v_self_4113_ = lean_ctor_get(v___y_4107_, 0);
lean_inc_ref(v_self_4113_);
lean_inc_ref(v_self_4112_);
v___x_4114_ = l_Lean_Meta_Grind_propagateCtor(v_self_4112_, v_self_4113_, v___y_4098_, v___y_4100_, v___y_4106_, v___y_4109_, v___y_4102_, v___y_4099_, v___y_4101_, v___y_4104_, v___y_4108_, v___y_4110_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_dec_ref_known(v___x_4114_, 1);
v___y_4070_ = v___y_4107_;
v___y_4071_ = v___y_4105_;
v___y_4072_ = v___y_4103_;
v___y_4073_ = v___y_4098_;
v___y_4074_ = v___y_4100_;
v___y_4075_ = v___y_4106_;
v___y_4076_ = v___y_4109_;
v___y_4077_ = v___y_4102_;
v___y_4078_ = v___y_4099_;
v___y_4079_ = v___y_4101_;
v___y_4080_ = v___y_4104_;
v___y_4081_ = v___y_4108_;
v___y_4082_ = v___y_4110_;
goto v___jp_4069_;
}
else
{
lean_dec_ref(v___y_4107_);
lean_dec_ref(v___y_4105_);
return v___x_4114_;
}
}
}
v___jp_4115_:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4119_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_a_4130_; uint8_t v___x_4131_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref_known(v___x_4129_, 1);
v___x_4131_ = lean_unbox(v_a_4130_);
lean_dec(v_a_4130_);
if (v___x_4131_ == 0)
{
uint8_t v_ctor_4132_; 
v_ctor_4132_ = lean_ctor_get_uint8(v___y_4117_, sizeof(void*)*12 + 2);
if (v_ctor_4132_ == 0)
{
v___y_4098_ = v___y_4119_;
v___y_4099_ = v___y_4124_;
v___y_4100_ = v___y_4120_;
v___y_4101_ = v___y_4125_;
v___y_4102_ = v___y_4123_;
v___y_4103_ = v___y_4118_;
v___y_4104_ = v___y_4126_;
v___y_4105_ = v___y_4117_;
v___y_4106_ = v___y_4121_;
v___y_4107_ = v___y_4116_;
v___y_4108_ = v___y_4127_;
v___y_4109_ = v___y_4122_;
v___y_4110_ = v___y_4128_;
v___y_4111_ = v___x_4029_;
goto v___jp_4097_;
}
else
{
uint8_t v_ctor_4133_; 
v_ctor_4133_ = lean_ctor_get_uint8(v___y_4116_, sizeof(void*)*12 + 2);
v___y_4098_ = v___y_4119_;
v___y_4099_ = v___y_4124_;
v___y_4100_ = v___y_4120_;
v___y_4101_ = v___y_4125_;
v___y_4102_ = v___y_4123_;
v___y_4103_ = v___y_4118_;
v___y_4104_ = v___y_4126_;
v___y_4105_ = v___y_4117_;
v___y_4106_ = v___y_4121_;
v___y_4107_ = v___y_4116_;
v___y_4108_ = v___y_4127_;
v___y_4109_ = v___y_4122_;
v___y_4110_ = v___y_4128_;
v___y_4111_ = v_ctor_4133_;
goto v___jp_4097_;
}
}
else
{
v___y_4070_ = v___y_4116_;
v___y_4071_ = v___y_4117_;
v___y_4072_ = v___y_4118_;
v___y_4073_ = v___y_4119_;
v___y_4074_ = v___y_4120_;
v___y_4075_ = v___y_4121_;
v___y_4076_ = v___y_4122_;
v___y_4077_ = v___y_4123_;
v___y_4078_ = v___y_4124_;
v___y_4079_ = v___y_4125_;
v___y_4080_ = v___y_4126_;
v___y_4081_ = v___y_4127_;
v___y_4082_ = v___y_4128_;
goto v___jp_4069_;
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec_ref(v___y_4117_);
lean_dec_ref(v___y_4116_);
v_a_4134_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4129_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4129_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
v___jp_4142_:
{
if (v___y_4144_ == 0)
{
v___y_4116_ = v___y_4143_;
v___y_4117_ = v___y_4146_;
v___y_4118_ = v___y_4145_;
v___y_4119_ = v___y_4147_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
goto v___jp_4115_;
}
else
{
lean_object* v___x_4157_; 
v___x_4157_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_dec_ref_known(v___x_4157_, 1);
v___y_4116_ = v___y_4143_;
v___y_4117_ = v___y_4146_;
v___y_4118_ = v___y_4145_;
v___y_4119_ = v___y_4147_;
v___y_4120_ = v___y_4148_;
v___y_4121_ = v___y_4149_;
v___y_4122_ = v___y_4150_;
v___y_4123_ = v___y_4151_;
v___y_4124_ = v___y_4152_;
v___y_4125_ = v___y_4153_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___y_4155_;
v___y_4128_ = v___y_4156_;
goto v___jp_4115_;
}
else
{
lean_dec_ref(v___y_4146_);
lean_dec_ref(v___y_4143_);
return v___x_4157_;
}
}
}
v___jp_4158_:
{
lean_object* v___x_4173_; 
lean_inc_ref(v___y_4167_);
lean_inc_ref(v___y_4168_);
v___x_4173_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4005_, v_isHEq_4006_, v_rhs_4004_, v_lhs_4003_, v_a_4026_, v_a_4023_, v___y_4168_, v___y_4167_, v___x_4033_, v___y_4170_, v___y_4172_, v___y_4163_, v___y_4165_, v___y_4169_, v___y_4161_, v___y_4160_, v___y_4162_, v___y_4171_, v___y_4164_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_dec_ref_known(v___x_4173_, 1);
v___y_4143_ = v___y_4168_;
v___y_4144_ = v___y_4159_;
v___y_4145_ = v___y_4166_;
v___y_4146_ = v___y_4167_;
v___y_4147_ = v___y_4170_;
v___y_4148_ = v___y_4172_;
v___y_4149_ = v___y_4163_;
v___y_4150_ = v___y_4165_;
v___y_4151_ = v___y_4169_;
v___y_4152_ = v___y_4161_;
v___y_4153_ = v___y_4160_;
v___y_4154_ = v___y_4162_;
v___y_4155_ = v___y_4171_;
v___y_4156_ = v___y_4164_;
goto v___jp_4142_;
}
else
{
lean_dec_ref(v___y_4168_);
lean_dec_ref(v___y_4167_);
return v___x_4173_;
}
}
v___jp_4174_:
{
lean_object* v___x_4189_; 
lean_inc_ref(v___y_4184_);
lean_inc_ref(v___y_4183_);
v___x_4189_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4005_, v_isHEq_4006_, v_lhs_4003_, v_rhs_4004_, v_a_4023_, v_a_4026_, v___y_4183_, v___y_4184_, v___x_4029_, v___y_4186_, v___y_4188_, v___y_4179_, v___y_4181_, v___y_4185_, v___y_4177_, v___y_4176_, v___y_4178_, v___y_4187_, v___y_4180_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_dec_ref_known(v___x_4189_, 1);
v___y_4143_ = v___y_4184_;
v___y_4144_ = v___y_4175_;
v___y_4145_ = v___y_4182_;
v___y_4146_ = v___y_4183_;
v___y_4147_ = v___y_4186_;
v___y_4148_ = v___y_4188_;
v___y_4149_ = v___y_4179_;
v___y_4150_ = v___y_4181_;
v___y_4151_ = v___y_4185_;
v___y_4152_ = v___y_4177_;
v___y_4153_ = v___y_4176_;
v___y_4154_ = v___y_4178_;
v___y_4155_ = v___y_4187_;
v___y_4156_ = v___y_4180_;
goto v___jp_4142_;
}
else
{
lean_dec_ref(v___y_4184_);
lean_dec_ref(v___y_4183_);
return v___x_4189_;
}
}
v___jp_4190_:
{
if (v___y_4205_ == 0)
{
v___y_4175_ = v___y_4191_;
v___y_4176_ = v___y_4192_;
v___y_4177_ = v___y_4193_;
v___y_4178_ = v___y_4194_;
v___y_4179_ = v___y_4195_;
v___y_4180_ = v___y_4196_;
v___y_4181_ = v___y_4197_;
v___y_4182_ = v___y_4198_;
v___y_4183_ = v___y_4199_;
v___y_4184_ = v___y_4200_;
v___y_4185_ = v___y_4201_;
v___y_4186_ = v___y_4202_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4204_;
goto v___jp_4174_;
}
else
{
v___y_4159_ = v___y_4191_;
v___y_4160_ = v___y_4192_;
v___y_4161_ = v___y_4193_;
v___y_4162_ = v___y_4194_;
v___y_4163_ = v___y_4195_;
v___y_4164_ = v___y_4196_;
v___y_4165_ = v___y_4197_;
v___y_4166_ = v___y_4198_;
v___y_4167_ = v___y_4199_;
v___y_4168_ = v___y_4200_;
v___y_4169_ = v___y_4201_;
v___y_4170_ = v___y_4202_;
v___y_4171_ = v___y_4203_;
v___y_4172_ = v___y_4204_;
goto v___jp_4158_;
}
}
v___jp_4206_:
{
uint8_t v___x_4225_; 
v___x_4225_ = lean_nat_dec_lt(v_size_4218_, v_size_4215_);
lean_dec(v_size_4215_);
lean_dec(v_size_4218_);
if (v___x_4225_ == 0)
{
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4208_;
v___y_4193_ = v___y_4209_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___y_4211_;
v___y_4196_ = v___y_4212_;
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4216_;
v___y_4199_ = v___y_4214_;
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4221_;
v___y_4202_ = v___y_4222_;
v___y_4203_ = v___y_4223_;
v___y_4204_ = v___y_4224_;
v___y_4205_ = v___x_4029_;
goto v___jp_4190_;
}
else
{
if (v_interpreted_4219_ == 0)
{
if (v___x_4225_ == 0)
{
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4208_;
v___y_4193_ = v___y_4209_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___y_4211_;
v___y_4196_ = v___y_4212_;
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4216_;
v___y_4199_ = v___y_4214_;
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4221_;
v___y_4202_ = v___y_4222_;
v___y_4203_ = v___y_4223_;
v___y_4204_ = v___y_4224_;
v___y_4205_ = v___x_4029_;
goto v___jp_4190_;
}
else
{
if (v_ctor_4220_ == 0)
{
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4208_;
v___y_4193_ = v___y_4209_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___y_4211_;
v___y_4196_ = v___y_4212_;
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4216_;
v___y_4199_ = v___y_4214_;
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4221_;
v___y_4202_ = v___y_4222_;
v___y_4203_ = v___y_4223_;
v___y_4204_ = v___y_4224_;
v___y_4205_ = v___x_4225_;
goto v___jp_4190_;
}
else
{
v___y_4175_ = v___y_4207_;
v___y_4176_ = v___y_4208_;
v___y_4177_ = v___y_4209_;
v___y_4178_ = v___y_4210_;
v___y_4179_ = v___y_4211_;
v___y_4180_ = v___y_4212_;
v___y_4181_ = v___y_4213_;
v___y_4182_ = v___y_4216_;
v___y_4183_ = v___y_4214_;
v___y_4184_ = v___y_4217_;
v___y_4185_ = v___y_4221_;
v___y_4186_ = v___y_4222_;
v___y_4187_ = v___y_4223_;
v___y_4188_ = v___y_4224_;
goto v___jp_4174_;
}
}
}
else
{
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4208_;
v___y_4193_ = v___y_4209_;
v___y_4194_ = v___y_4210_;
v___y_4195_ = v___y_4211_;
v___y_4196_ = v___y_4212_;
v___y_4197_ = v___y_4213_;
v___y_4198_ = v___y_4216_;
v___y_4199_ = v___y_4214_;
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4221_;
v___y_4202_ = v___y_4222_;
v___y_4203_ = v___y_4223_;
v___y_4204_ = v___y_4224_;
v___y_4205_ = v___x_4029_;
goto v___jp_4190_;
}
}
}
v___jp_4226_:
{
if (v___y_4241_ == 0)
{
uint8_t v_ctor_4242_; 
v_ctor_4242_ = lean_ctor_get_uint8(v___y_4234_, sizeof(void*)*12 + 2);
if (v_ctor_4242_ == 0)
{
if (v___x_4029_ == 0)
{
lean_object* v_size_4243_; lean_object* v_size_4244_; uint8_t v_interpreted_4245_; uint8_t v_ctor_4246_; 
v_size_4243_ = lean_ctor_get(v___y_4234_, 6);
lean_inc(v_size_4243_);
v_size_4244_ = lean_ctor_get(v___y_4236_, 6);
lean_inc(v_size_4244_);
v_interpreted_4245_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 1);
v_ctor_4246_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 2);
v___y_4207_ = v___y_4227_;
v___y_4208_ = v___y_4228_;
v___y_4209_ = v___y_4229_;
v___y_4210_ = v___y_4230_;
v___y_4211_ = v___y_4231_;
v___y_4212_ = v___y_4232_;
v___y_4213_ = v___y_4233_;
v___y_4214_ = v___y_4234_;
v_size_4215_ = v_size_4243_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v_size_4218_ = v_size_4244_;
v_interpreted_4219_ = v_interpreted_4245_;
v_ctor_4220_ = v_ctor_4246_;
v___y_4221_ = v___y_4237_;
v___y_4222_ = v___y_4238_;
v___y_4223_ = v___y_4239_;
v___y_4224_ = v___y_4240_;
goto v___jp_4206_;
}
else
{
v___y_4159_ = v___y_4227_;
v___y_4160_ = v___y_4228_;
v___y_4161_ = v___y_4229_;
v___y_4162_ = v___y_4230_;
v___y_4163_ = v___y_4231_;
v___y_4164_ = v___y_4232_;
v___y_4165_ = v___y_4233_;
v___y_4166_ = v___y_4235_;
v___y_4167_ = v___y_4234_;
v___y_4168_ = v___y_4236_;
v___y_4169_ = v___y_4237_;
v___y_4170_ = v___y_4238_;
v___y_4171_ = v___y_4239_;
v___y_4172_ = v___y_4240_;
goto v___jp_4158_;
}
}
else
{
uint8_t v_ctor_4247_; 
v_ctor_4247_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 2);
if (v_ctor_4247_ == 0)
{
v___y_4159_ = v___y_4227_;
v___y_4160_ = v___y_4228_;
v___y_4161_ = v___y_4229_;
v___y_4162_ = v___y_4230_;
v___y_4163_ = v___y_4231_;
v___y_4164_ = v___y_4232_;
v___y_4165_ = v___y_4233_;
v___y_4166_ = v___y_4235_;
v___y_4167_ = v___y_4234_;
v___y_4168_ = v___y_4236_;
v___y_4169_ = v___y_4237_;
v___y_4170_ = v___y_4238_;
v___y_4171_ = v___y_4239_;
v___y_4172_ = v___y_4240_;
goto v___jp_4158_;
}
else
{
lean_object* v_size_4248_; lean_object* v_size_4249_; uint8_t v_interpreted_4250_; 
v_size_4248_ = lean_ctor_get(v___y_4234_, 6);
lean_inc(v_size_4248_);
v_size_4249_ = lean_ctor_get(v___y_4236_, 6);
lean_inc(v_size_4249_);
v_interpreted_4250_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 1);
v___y_4207_ = v___y_4227_;
v___y_4208_ = v___y_4228_;
v___y_4209_ = v___y_4229_;
v___y_4210_ = v___y_4230_;
v___y_4211_ = v___y_4231_;
v___y_4212_ = v___y_4232_;
v___y_4213_ = v___y_4233_;
v___y_4214_ = v___y_4234_;
v_size_4215_ = v_size_4248_;
v___y_4216_ = v___y_4235_;
v___y_4217_ = v___y_4236_;
v_size_4218_ = v_size_4249_;
v_interpreted_4219_ = v_interpreted_4250_;
v_ctor_4220_ = v_ctor_4247_;
v___y_4221_ = v___y_4237_;
v___y_4222_ = v___y_4238_;
v___y_4223_ = v___y_4239_;
v___y_4224_ = v___y_4240_;
goto v___jp_4206_;
}
}
}
else
{
v___y_4159_ = v___y_4227_;
v___y_4160_ = v___y_4228_;
v___y_4161_ = v___y_4229_;
v___y_4162_ = v___y_4230_;
v___y_4163_ = v___y_4231_;
v___y_4164_ = v___y_4232_;
v___y_4165_ = v___y_4233_;
v___y_4166_ = v___y_4235_;
v___y_4167_ = v___y_4234_;
v___y_4168_ = v___y_4236_;
v___y_4169_ = v___y_4237_;
v___y_4170_ = v___y_4238_;
v___y_4171_ = v___y_4239_;
v___y_4172_ = v___y_4240_;
goto v___jp_4158_;
}
}
v___jp_4251_:
{
if (v_interpreted_4254_ == 0)
{
v___y_4227_ = v_trueEqFalse_4256_;
v___y_4228_ = v___y_4263_;
v___y_4229_ = v___y_4262_;
v___y_4230_ = v___y_4264_;
v___y_4231_ = v___y_4259_;
v___y_4232_ = v___y_4266_;
v___y_4233_ = v___y_4260_;
v___y_4234_ = v___y_4253_;
v___y_4235_ = v_valueInconsistency_4255_;
v___y_4236_ = v___y_4252_;
v___y_4237_ = v___y_4261_;
v___y_4238_ = v___y_4257_;
v___y_4239_ = v___y_4265_;
v___y_4240_ = v___y_4258_;
v___y_4241_ = v___x_4029_;
goto v___jp_4226_;
}
else
{
uint8_t v_interpreted_4267_; 
v_interpreted_4267_ = lean_ctor_get_uint8(v___y_4252_, sizeof(void*)*12 + 1);
if (v_interpreted_4267_ == 0)
{
v___y_4159_ = v_trueEqFalse_4256_;
v___y_4160_ = v___y_4263_;
v___y_4161_ = v___y_4262_;
v___y_4162_ = v___y_4264_;
v___y_4163_ = v___y_4259_;
v___y_4164_ = v___y_4266_;
v___y_4165_ = v___y_4260_;
v___y_4166_ = v_valueInconsistency_4255_;
v___y_4167_ = v___y_4253_;
v___y_4168_ = v___y_4252_;
v___y_4169_ = v___y_4261_;
v___y_4170_ = v___y_4257_;
v___y_4171_ = v___y_4265_;
v___y_4172_ = v___y_4258_;
goto v___jp_4158_;
}
else
{
v___y_4227_ = v_trueEqFalse_4256_;
v___y_4228_ = v___y_4263_;
v___y_4229_ = v___y_4262_;
v___y_4230_ = v___y_4264_;
v___y_4231_ = v___y_4259_;
v___y_4232_ = v___y_4266_;
v___y_4233_ = v___y_4260_;
v___y_4234_ = v___y_4253_;
v___y_4235_ = v_valueInconsistency_4255_;
v___y_4236_ = v___y_4252_;
v___y_4237_ = v___y_4261_;
v___y_4238_ = v___y_4257_;
v___y_4239_ = v___y_4265_;
v___y_4240_ = v___y_4258_;
v___y_4241_ = v___x_4029_;
goto v___jp_4226_;
}
}
}
v___jp_4268_:
{
uint8_t v_interpreted_4283_; 
v_interpreted_4283_ = lean_ctor_get_uint8(v___y_4270_, sizeof(void*)*12 + 1);
v___y_4252_ = v___y_4269_;
v___y_4253_ = v___y_4270_;
v_interpreted_4254_ = v_interpreted_4283_;
v_valueInconsistency_4255_ = v_valueInconsistency_4271_;
v_trueEqFalse_4256_ = v_trueEqFalse_4272_;
v___y_4257_ = v___y_4273_;
v___y_4258_ = v___y_4274_;
v___y_4259_ = v___y_4275_;
v___y_4260_ = v___y_4276_;
v___y_4261_ = v___y_4277_;
v___y_4262_ = v___y_4278_;
v___y_4263_ = v___y_4279_;
v___y_4264_ = v___y_4280_;
v___y_4265_ = v___y_4281_;
v___y_4266_ = v___y_4282_;
goto v___jp_4251_;
}
v___jp_4284_:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4286_, v___y_4290_, v___y_4285_, v___y_4295_, v___y_4287_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_dec_ref_known(v___x_4297_, 1);
v___y_4269_ = v___y_4293_;
v___y_4270_ = v___y_4289_;
v_valueInconsistency_4271_ = v___x_4029_;
v_trueEqFalse_4272_ = v___x_4033_;
v___y_4273_ = v___y_4286_;
v___y_4274_ = v___y_4288_;
v___y_4275_ = v___y_4291_;
v___y_4276_ = v___y_4296_;
v___y_4277_ = v___y_4292_;
v___y_4278_ = v___y_4294_;
v___y_4279_ = v___y_4290_;
v___y_4280_ = v___y_4285_;
v___y_4281_ = v___y_4295_;
v___y_4282_ = v___y_4287_;
goto v___jp_4268_;
}
else
{
lean_dec_ref(v___y_4293_);
lean_dec_ref(v___y_4289_);
lean_dec(v_a_4026_);
lean_dec(v_a_4023_);
lean_dec_ref(v_proof_4005_);
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
return v___x_4297_;
}
}
v___jp_4298_:
{
if (v___y_4310_ == 0)
{
lean_object* v_self_4312_; uint8_t v_interpreted_4313_; lean_object* v_self_4314_; lean_object* v___x_4315_; 
v_self_4312_ = lean_ctor_get(v___y_4302_, 0);
v_interpreted_4313_ = lean_ctor_get_uint8(v___y_4302_, sizeof(void*)*12 + 1);
v_self_4314_ = lean_ctor_get(v___y_4307_, 0);
lean_inc_ref(v_self_4314_);
lean_inc_ref(v_self_4312_);
v___x_4315_ = l_Lean_Meta_Grind_hasSameType(v_self_4312_, v_self_4314_, v___y_4304_, v___y_4299_, v___y_4309_, v___y_4301_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; uint8_t v___x_4317_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc(v_a_4316_);
lean_dec_ref_known(v___x_4315_, 1);
v___x_4317_ = lean_unbox(v_a_4316_);
lean_dec(v_a_4316_);
if (v___x_4317_ == 0)
{
v___y_4252_ = v___y_4307_;
v___y_4253_ = v___y_4302_;
v_interpreted_4254_ = v_interpreted_4313_;
v_valueInconsistency_4255_ = v___x_4029_;
v_trueEqFalse_4256_ = v___x_4029_;
v___y_4257_ = v___y_4300_;
v___y_4258_ = v___y_4303_;
v___y_4259_ = v___y_4305_;
v___y_4260_ = v___y_4311_;
v___y_4261_ = v___y_4306_;
v___y_4262_ = v___y_4308_;
v___y_4263_ = v___y_4304_;
v___y_4264_ = v___y_4299_;
v___y_4265_ = v___y_4309_;
v___y_4266_ = v___y_4301_;
goto v___jp_4251_;
}
else
{
v___y_4252_ = v___y_4307_;
v___y_4253_ = v___y_4302_;
v_interpreted_4254_ = v_interpreted_4313_;
v_valueInconsistency_4255_ = v___x_4033_;
v_trueEqFalse_4256_ = v___x_4029_;
v___y_4257_ = v___y_4300_;
v___y_4258_ = v___y_4303_;
v___y_4259_ = v___y_4305_;
v___y_4260_ = v___y_4311_;
v___y_4261_ = v___y_4306_;
v___y_4262_ = v___y_4308_;
v___y_4263_ = v___y_4304_;
v___y_4264_ = v___y_4299_;
v___y_4265_ = v___y_4309_;
v___y_4266_ = v___y_4301_;
goto v___jp_4251_;
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec_ref(v___y_4307_);
lean_dec_ref(v___y_4302_);
lean_dec(v_a_4026_);
lean_dec(v_a_4023_);
lean_dec_ref(v_proof_4005_);
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
v_a_4318_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4315_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4315_);
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
v___y_4269_ = v___y_4307_;
v___y_4270_ = v___y_4302_;
v_valueInconsistency_4271_ = v___x_4033_;
v_trueEqFalse_4272_ = v___x_4029_;
v___y_4273_ = v___y_4300_;
v___y_4274_ = v___y_4303_;
v___y_4275_ = v___y_4305_;
v___y_4276_ = v___y_4311_;
v___y_4277_ = v___y_4306_;
v___y_4278_ = v___y_4308_;
v___y_4279_ = v___y_4304_;
v___y_4280_ = v___y_4299_;
v___y_4281_ = v___y_4309_;
v___y_4282_ = v___y_4301_;
goto v___jp_4268_;
}
}
v___jp_4326_:
{
if (v___y_4339_ == 0)
{
v___y_4269_ = v___y_4335_;
v___y_4270_ = v___y_4331_;
v_valueInconsistency_4271_ = v___x_4029_;
v_trueEqFalse_4272_ = v___x_4029_;
v___y_4273_ = v___y_4328_;
v___y_4274_ = v___y_4330_;
v___y_4275_ = v___y_4332_;
v___y_4276_ = v___y_4338_;
v___y_4277_ = v___y_4333_;
v___y_4278_ = v___y_4336_;
v___y_4279_ = v___y_4334_;
v___y_4280_ = v___y_4327_;
v___y_4281_ = v___y_4337_;
v___y_4282_ = v___y_4329_;
goto v___jp_4268_;
}
else
{
uint8_t v___x_4340_; 
lean_inc_ref(v_root_4027_);
v___x_4340_ = l_Lean_Expr_isTrue(v_root_4027_);
if (v___x_4340_ == 0)
{
uint8_t v___x_4341_; 
lean_inc_ref(v_root_4028_);
v___x_4341_ = l_Lean_Expr_isTrue(v_root_4028_);
if (v___x_4341_ == 0)
{
if (v_isHEq_4006_ == 0)
{
uint8_t v_heqProofs_4342_; 
v_heqProofs_4342_ = lean_ctor_get_uint8(v___y_4331_, sizeof(void*)*12 + 4);
if (v_heqProofs_4342_ == 0)
{
uint8_t v_heqProofs_4343_; 
v_heqProofs_4343_ = lean_ctor_get_uint8(v___y_4335_, sizeof(void*)*12 + 4);
if (v_heqProofs_4343_ == 0)
{
uint8_t v_interpreted_4344_; 
v_interpreted_4344_ = lean_ctor_get_uint8(v___y_4331_, sizeof(void*)*12 + 1);
v___y_4252_ = v___y_4335_;
v___y_4253_ = v___y_4331_;
v_interpreted_4254_ = v_interpreted_4344_;
v_valueInconsistency_4255_ = v___x_4033_;
v_trueEqFalse_4256_ = v___x_4029_;
v___y_4257_ = v___y_4328_;
v___y_4258_ = v___y_4330_;
v___y_4259_ = v___y_4332_;
v___y_4260_ = v___y_4338_;
v___y_4261_ = v___y_4333_;
v___y_4262_ = v___y_4336_;
v___y_4263_ = v___y_4334_;
v___y_4264_ = v___y_4327_;
v___y_4265_ = v___y_4337_;
v___y_4266_ = v___y_4329_;
goto v___jp_4251_;
}
else
{
v___y_4299_ = v___y_4327_;
v___y_4300_ = v___y_4328_;
v___y_4301_ = v___y_4329_;
v___y_4302_ = v___y_4331_;
v___y_4303_ = v___y_4330_;
v___y_4304_ = v___y_4334_;
v___y_4305_ = v___y_4332_;
v___y_4306_ = v___y_4333_;
v___y_4307_ = v___y_4335_;
v___y_4308_ = v___y_4336_;
v___y_4309_ = v___y_4337_;
v___y_4310_ = v___x_4341_;
v___y_4311_ = v___y_4338_;
goto v___jp_4298_;
}
}
else
{
v___y_4299_ = v___y_4327_;
v___y_4300_ = v___y_4328_;
v___y_4301_ = v___y_4329_;
v___y_4302_ = v___y_4331_;
v___y_4303_ = v___y_4330_;
v___y_4304_ = v___y_4334_;
v___y_4305_ = v___y_4332_;
v___y_4306_ = v___y_4333_;
v___y_4307_ = v___y_4335_;
v___y_4308_ = v___y_4336_;
v___y_4309_ = v___y_4337_;
v___y_4310_ = v___x_4341_;
v___y_4311_ = v___y_4338_;
goto v___jp_4298_;
}
}
else
{
v___y_4299_ = v___y_4327_;
v___y_4300_ = v___y_4328_;
v___y_4301_ = v___y_4329_;
v___y_4302_ = v___y_4331_;
v___y_4303_ = v___y_4330_;
v___y_4304_ = v___y_4334_;
v___y_4305_ = v___y_4332_;
v___y_4306_ = v___y_4333_;
v___y_4307_ = v___y_4335_;
v___y_4308_ = v___y_4336_;
v___y_4309_ = v___y_4337_;
v___y_4310_ = v___x_4341_;
v___y_4311_ = v___y_4338_;
goto v___jp_4298_;
}
}
else
{
v___y_4285_ = v___y_4327_;
v___y_4286_ = v___y_4328_;
v___y_4287_ = v___y_4329_;
v___y_4288_ = v___y_4330_;
v___y_4289_ = v___y_4331_;
v___y_4290_ = v___y_4334_;
v___y_4291_ = v___y_4332_;
v___y_4292_ = v___y_4333_;
v___y_4293_ = v___y_4335_;
v___y_4294_ = v___y_4336_;
v___y_4295_ = v___y_4337_;
v___y_4296_ = v___y_4338_;
goto v___jp_4284_;
}
}
else
{
v___y_4285_ = v___y_4327_;
v___y_4286_ = v___y_4328_;
v___y_4287_ = v___y_4329_;
v___y_4288_ = v___y_4330_;
v___y_4289_ = v___y_4331_;
v___y_4290_ = v___y_4334_;
v___y_4291_ = v___y_4332_;
v___y_4292_ = v___y_4333_;
v___y_4293_ = v___y_4335_;
v___y_4294_ = v___y_4336_;
v___y_4295_ = v___y_4337_;
v___y_4296_ = v___y_4338_;
goto v___jp_4284_;
}
}
}
v___jp_4345_:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4356_ = lean_st_ref_get(v___y_4346_);
lean_inc_ref(v_root_4027_);
v___x_4357_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4356_, v_root_4027_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
lean_dec(v___x_4356_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v___x_4359_ = lean_st_ref_get(v___y_4346_);
lean_inc_ref(v_root_4028_);
v___x_4360_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4359_, v_root_4028_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
lean_dec(v___x_4359_);
if (lean_obj_tag(v___x_4360_) == 0)
{
uint8_t v_interpreted_4361_; 
v_interpreted_4361_ = lean_ctor_get_uint8(v_a_4358_, sizeof(void*)*12 + 1);
if (v_interpreted_4361_ == 0)
{
lean_object* v_a_4362_; 
v_a_4362_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4360_, 1);
v___y_4327_ = v___y_4353_;
v___y_4328_ = v___y_4346_;
v___y_4329_ = v___y_4355_;
v___y_4330_ = v___y_4347_;
v___y_4331_ = v_a_4358_;
v___y_4332_ = v___y_4348_;
v___y_4333_ = v___y_4350_;
v___y_4334_ = v___y_4352_;
v___y_4335_ = v_a_4362_;
v___y_4336_ = v___y_4351_;
v___y_4337_ = v___y_4354_;
v___y_4338_ = v___y_4349_;
v___y_4339_ = v___x_4029_;
goto v___jp_4326_;
}
else
{
lean_object* v_a_4363_; uint8_t v_interpreted_4364_; 
v_a_4363_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4360_, 1);
v_interpreted_4364_ = lean_ctor_get_uint8(v_a_4363_, sizeof(void*)*12 + 1);
v___y_4327_ = v___y_4353_;
v___y_4328_ = v___y_4346_;
v___y_4329_ = v___y_4355_;
v___y_4330_ = v___y_4347_;
v___y_4331_ = v_a_4358_;
v___y_4332_ = v___y_4348_;
v___y_4333_ = v___y_4350_;
v___y_4334_ = v___y_4352_;
v___y_4335_ = v_a_4363_;
v___y_4336_ = v___y_4351_;
v___y_4337_ = v___y_4354_;
v___y_4338_ = v___y_4349_;
v___y_4339_ = v_interpreted_4364_;
goto v___jp_4326_;
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_dec(v_a_4358_);
lean_dec(v_a_4026_);
lean_dec(v_a_4023_);
lean_dec_ref(v_proof_4005_);
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
v_a_4365_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4360_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4360_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v_a_4026_);
lean_dec(v_a_4023_);
lean_dec_ref(v_proof_4005_);
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
v_a_4373_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4357_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4357_);
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
lean_object* v_options_4419_; uint8_t v_hasTrace_4420_; 
lean_dec(v_a_4026_);
lean_dec(v_a_4023_);
lean_dec_ref(v_proof_4005_);
v_options_4419_ = lean_ctor_get(v_a_4015_, 2);
v_hasTrace_4420_ = lean_ctor_get_uint8(v_options_4419_, sizeof(void*)*1);
if (v_hasTrace_4420_ == 0)
{
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
goto v___jp_4018_;
}
else
{
lean_object* v_inheritedTraceOptions_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; uint8_t v___x_4424_; 
v_inheritedTraceOptions_4421_ = lean_ctor_get(v_a_4015_, 13);
v___x_4422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4423_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4424_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4421_, v_options_4419_, v___x_4423_);
if (v___x_4424_ == 0)
{
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
goto v___jp_4018_;
}
else
{
lean_object* v___x_4425_; 
v___x_4425_ = l_Lean_Meta_Grind_updateLastTag(v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v___x_4426_; 
lean_dec_ref_known(v___x_4425_, 1);
v___x_4426_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4003_, v_a_4007_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4428_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
lean_dec_ref_known(v___x_4426_, 1);
v___x_4428_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4004_, v_a_4007_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v_a_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
lean_inc(v_a_4429_);
lean_dec_ref_known(v___x_4428_, 1);
v___x_4430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4431_, 0, v_a_4427_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
v___x_4432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
lean_ctor_set(v___x_4432_, 1, v_a_4429_);
v___x_4433_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4432_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
v___x_4435_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4422_, v___x_4434_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_dec_ref_known(v___x_4435_, 1);
goto v___jp_4018_;
}
else
{
return v___x_4435_;
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec(v_a_4427_);
v_a_4436_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4428_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4428_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
lean_dec_ref(v_rhs_4004_);
v_a_4444_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4426_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4426_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
return v___x_4425_;
}
}
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec(v_a_4023_);
lean_dec_ref(v_proof_4005_);
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
v_a_4452_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4025_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4025_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec_ref(v_proof_4005_);
lean_dec_ref(v_rhs_4004_);
lean_dec_ref(v_lhs_4003_);
v_a_4460_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4022_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4022_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
v___jp_4018_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4019_ = lean_box(0);
v___x_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
return v___x_4020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4468_, lean_object* v_rhs_4469_, lean_object* v_proof_4470_, lean_object* v_isHEq_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
uint8_t v_isHEq_boxed_4483_; lean_object* v_res_4484_; 
v_isHEq_boxed_4483_ = lean_unbox(v_isHEq_4471_);
v_res_4484_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4468_, v_rhs_4469_, v_proof_4470_, v_isHEq_boxed_4483_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
lean_dec(v_a_4475_);
lean_dec_ref(v_a_4474_);
lean_dec(v_a_4473_);
lean_dec(v_a_4472_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4487_){
_start:
{
lean_object* v___x_4489_; lean_object* v_toGoalState_4490_; lean_object* v_mvarId_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4527_; 
v___x_4489_ = lean_st_ref_take(v_a_4487_);
v_toGoalState_4490_ = lean_ctor_get(v___x_4489_, 0);
v_mvarId_4491_ = lean_ctor_get(v___x_4489_, 1);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4493_ = v___x_4489_;
v_isShared_4494_ = v_isSharedCheck_4527_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_mvarId_4491_);
lean_inc(v_toGoalState_4490_);
lean_dec(v___x_4489_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4527_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v_nextDeclIdx_4495_; lean_object* v_enodeMap_4496_; lean_object* v_exprs_4497_; lean_object* v_parents_4498_; lean_object* v_congrTable_4499_; lean_object* v_appMap_4500_; lean_object* v_indicesFound_4501_; uint8_t v_inconsistent_4502_; lean_object* v_nextIdx_4503_; lean_object* v_newRawFacts_4504_; lean_object* v_facts_4505_; lean_object* v_extThms_4506_; lean_object* v_ematch_4507_; lean_object* v_inj_4508_; lean_object* v_split_4509_; lean_object* v_clean_4510_; lean_object* v_sstates_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4525_; 
v_nextDeclIdx_4495_ = lean_ctor_get(v_toGoalState_4490_, 0);
v_enodeMap_4496_ = lean_ctor_get(v_toGoalState_4490_, 1);
v_exprs_4497_ = lean_ctor_get(v_toGoalState_4490_, 2);
v_parents_4498_ = lean_ctor_get(v_toGoalState_4490_, 3);
v_congrTable_4499_ = lean_ctor_get(v_toGoalState_4490_, 4);
v_appMap_4500_ = lean_ctor_get(v_toGoalState_4490_, 5);
v_indicesFound_4501_ = lean_ctor_get(v_toGoalState_4490_, 6);
v_inconsistent_4502_ = lean_ctor_get_uint8(v_toGoalState_4490_, sizeof(void*)*17);
v_nextIdx_4503_ = lean_ctor_get(v_toGoalState_4490_, 8);
v_newRawFacts_4504_ = lean_ctor_get(v_toGoalState_4490_, 9);
v_facts_4505_ = lean_ctor_get(v_toGoalState_4490_, 10);
v_extThms_4506_ = lean_ctor_get(v_toGoalState_4490_, 11);
v_ematch_4507_ = lean_ctor_get(v_toGoalState_4490_, 12);
v_inj_4508_ = lean_ctor_get(v_toGoalState_4490_, 13);
v_split_4509_ = lean_ctor_get(v_toGoalState_4490_, 14);
v_clean_4510_ = lean_ctor_get(v_toGoalState_4490_, 15);
v_sstates_4511_ = lean_ctor_get(v_toGoalState_4490_, 16);
v_isSharedCheck_4525_ = !lean_is_exclusive(v_toGoalState_4490_);
if (v_isSharedCheck_4525_ == 0)
{
lean_object* v_unused_4526_; 
v_unused_4526_ = lean_ctor_get(v_toGoalState_4490_, 7);
lean_dec(v_unused_4526_);
v___x_4513_ = v_toGoalState_4490_;
v_isShared_4514_ = v_isSharedCheck_4525_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_sstates_4511_);
lean_inc(v_clean_4510_);
lean_inc(v_split_4509_);
lean_inc(v_inj_4508_);
lean_inc(v_ematch_4507_);
lean_inc(v_extThms_4506_);
lean_inc(v_facts_4505_);
lean_inc(v_newRawFacts_4504_);
lean_inc(v_nextIdx_4503_);
lean_inc(v_indicesFound_4501_);
lean_inc(v_appMap_4500_);
lean_inc(v_congrTable_4499_);
lean_inc(v_parents_4498_);
lean_inc(v_exprs_4497_);
lean_inc(v_enodeMap_4496_);
lean_inc(v_nextDeclIdx_4495_);
lean_dec(v_toGoalState_4490_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4525_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4515_; lean_object* v___x_4517_; 
v___x_4515_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 7, v___x_4515_);
v___x_4517_ = v___x_4513_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_nextDeclIdx_4495_);
lean_ctor_set(v_reuseFailAlloc_4524_, 1, v_enodeMap_4496_);
lean_ctor_set(v_reuseFailAlloc_4524_, 2, v_exprs_4497_);
lean_ctor_set(v_reuseFailAlloc_4524_, 3, v_parents_4498_);
lean_ctor_set(v_reuseFailAlloc_4524_, 4, v_congrTable_4499_);
lean_ctor_set(v_reuseFailAlloc_4524_, 5, v_appMap_4500_);
lean_ctor_set(v_reuseFailAlloc_4524_, 6, v_indicesFound_4501_);
lean_ctor_set(v_reuseFailAlloc_4524_, 7, v___x_4515_);
lean_ctor_set(v_reuseFailAlloc_4524_, 8, v_nextIdx_4503_);
lean_ctor_set(v_reuseFailAlloc_4524_, 9, v_newRawFacts_4504_);
lean_ctor_set(v_reuseFailAlloc_4524_, 10, v_facts_4505_);
lean_ctor_set(v_reuseFailAlloc_4524_, 11, v_extThms_4506_);
lean_ctor_set(v_reuseFailAlloc_4524_, 12, v_ematch_4507_);
lean_ctor_set(v_reuseFailAlloc_4524_, 13, v_inj_4508_);
lean_ctor_set(v_reuseFailAlloc_4524_, 14, v_split_4509_);
lean_ctor_set(v_reuseFailAlloc_4524_, 15, v_clean_4510_);
lean_ctor_set(v_reuseFailAlloc_4524_, 16, v_sstates_4511_);
lean_ctor_set_uint8(v_reuseFailAlloc_4524_, sizeof(void*)*17, v_inconsistent_4502_);
v___x_4517_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4519_; 
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 0, v___x_4517_);
v___x_4519_ = v___x_4493_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4517_);
lean_ctor_set(v_reuseFailAlloc_4523_, 1, v_mvarId_4491_);
v___x_4519_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4520_ = lean_st_ref_set(v_a_4487_, v___x_4519_);
v___x_4521_ = lean_box(0);
v___x_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
return v___x_4522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4528_);
lean_dec(v_a_4528_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4531_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec(v_a_4543_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4555_){
_start:
{
lean_object* v___x_4557_; lean_object* v_toGoalState_4558_; lean_object* v_newFacts_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v___x_4557_ = lean_st_ref_get(v_a_4555_);
v_toGoalState_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc_ref(v_toGoalState_4558_);
lean_dec(v___x_4557_);
v_newFacts_4559_ = lean_ctor_get(v_toGoalState_4558_, 7);
lean_inc_ref(v_newFacts_4559_);
lean_dec_ref(v_toGoalState_4558_);
v___x_4560_ = lean_array_get_size(v_newFacts_4559_);
v___x_4561_ = lean_unsigned_to_nat(1u);
v___x_4562_ = lean_nat_sub(v___x_4560_, v___x_4561_);
v___x_4563_ = lean_nat_dec_lt(v___x_4562_, v___x_4560_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
lean_dec(v___x_4562_);
lean_dec_ref(v_newFacts_4559_);
v___x_4564_ = lean_box(0);
v___x_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4564_);
return v___x_4565_;
}
else
{
lean_object* v___x_4566_; lean_object* v_toGoalState_4567_; lean_object* v_mvarId_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4605_; 
v___x_4566_ = lean_st_ref_take(v_a_4555_);
v_toGoalState_4567_ = lean_ctor_get(v___x_4566_, 0);
v_mvarId_4568_ = lean_ctor_get(v___x_4566_, 1);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4570_ = v___x_4566_;
v_isShared_4571_ = v_isSharedCheck_4605_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_mvarId_4568_);
lean_inc(v_toGoalState_4567_);
lean_dec(v___x_4566_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4605_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v_nextDeclIdx_4572_; lean_object* v_enodeMap_4573_; lean_object* v_exprs_4574_; lean_object* v_parents_4575_; lean_object* v_congrTable_4576_; lean_object* v_appMap_4577_; lean_object* v_indicesFound_4578_; lean_object* v_newFacts_4579_; uint8_t v_inconsistent_4580_; lean_object* v_nextIdx_4581_; lean_object* v_newRawFacts_4582_; lean_object* v_facts_4583_; lean_object* v_extThms_4584_; lean_object* v_ematch_4585_; lean_object* v_inj_4586_; lean_object* v_split_4587_; lean_object* v_clean_4588_; lean_object* v_sstates_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4604_; 
v_nextDeclIdx_4572_ = lean_ctor_get(v_toGoalState_4567_, 0);
v_enodeMap_4573_ = lean_ctor_get(v_toGoalState_4567_, 1);
v_exprs_4574_ = lean_ctor_get(v_toGoalState_4567_, 2);
v_parents_4575_ = lean_ctor_get(v_toGoalState_4567_, 3);
v_congrTable_4576_ = lean_ctor_get(v_toGoalState_4567_, 4);
v_appMap_4577_ = lean_ctor_get(v_toGoalState_4567_, 5);
v_indicesFound_4578_ = lean_ctor_get(v_toGoalState_4567_, 6);
v_newFacts_4579_ = lean_ctor_get(v_toGoalState_4567_, 7);
v_inconsistent_4580_ = lean_ctor_get_uint8(v_toGoalState_4567_, sizeof(void*)*17);
v_nextIdx_4581_ = lean_ctor_get(v_toGoalState_4567_, 8);
v_newRawFacts_4582_ = lean_ctor_get(v_toGoalState_4567_, 9);
v_facts_4583_ = lean_ctor_get(v_toGoalState_4567_, 10);
v_extThms_4584_ = lean_ctor_get(v_toGoalState_4567_, 11);
v_ematch_4585_ = lean_ctor_get(v_toGoalState_4567_, 12);
v_inj_4586_ = lean_ctor_get(v_toGoalState_4567_, 13);
v_split_4587_ = lean_ctor_get(v_toGoalState_4567_, 14);
v_clean_4588_ = lean_ctor_get(v_toGoalState_4567_, 15);
v_sstates_4589_ = lean_ctor_get(v_toGoalState_4567_, 16);
v_isSharedCheck_4604_ = !lean_is_exclusive(v_toGoalState_4567_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4591_ = v_toGoalState_4567_;
v_isShared_4592_ = v_isSharedCheck_4604_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_sstates_4589_);
lean_inc(v_clean_4588_);
lean_inc(v_split_4587_);
lean_inc(v_inj_4586_);
lean_inc(v_ematch_4585_);
lean_inc(v_extThms_4584_);
lean_inc(v_facts_4583_);
lean_inc(v_newRawFacts_4582_);
lean_inc(v_nextIdx_4581_);
lean_inc(v_newFacts_4579_);
lean_inc(v_indicesFound_4578_);
lean_inc(v_appMap_4577_);
lean_inc(v_congrTable_4576_);
lean_inc(v_parents_4575_);
lean_inc(v_exprs_4574_);
lean_inc(v_enodeMap_4573_);
lean_inc(v_nextDeclIdx_4572_);
lean_dec(v_toGoalState_4567_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4604_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4593_; lean_object* v___x_4595_; 
v___x_4593_ = lean_array_pop(v_newFacts_4579_);
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 7, v___x_4593_);
v___x_4595_ = v___x_4591_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_nextDeclIdx_4572_);
lean_ctor_set(v_reuseFailAlloc_4603_, 1, v_enodeMap_4573_);
lean_ctor_set(v_reuseFailAlloc_4603_, 2, v_exprs_4574_);
lean_ctor_set(v_reuseFailAlloc_4603_, 3, v_parents_4575_);
lean_ctor_set(v_reuseFailAlloc_4603_, 4, v_congrTable_4576_);
lean_ctor_set(v_reuseFailAlloc_4603_, 5, v_appMap_4577_);
lean_ctor_set(v_reuseFailAlloc_4603_, 6, v_indicesFound_4578_);
lean_ctor_set(v_reuseFailAlloc_4603_, 7, v___x_4593_);
lean_ctor_set(v_reuseFailAlloc_4603_, 8, v_nextIdx_4581_);
lean_ctor_set(v_reuseFailAlloc_4603_, 9, v_newRawFacts_4582_);
lean_ctor_set(v_reuseFailAlloc_4603_, 10, v_facts_4583_);
lean_ctor_set(v_reuseFailAlloc_4603_, 11, v_extThms_4584_);
lean_ctor_set(v_reuseFailAlloc_4603_, 12, v_ematch_4585_);
lean_ctor_set(v_reuseFailAlloc_4603_, 13, v_inj_4586_);
lean_ctor_set(v_reuseFailAlloc_4603_, 14, v_split_4587_);
lean_ctor_set(v_reuseFailAlloc_4603_, 15, v_clean_4588_);
lean_ctor_set(v_reuseFailAlloc_4603_, 16, v_sstates_4589_);
lean_ctor_set_uint8(v_reuseFailAlloc_4603_, sizeof(void*)*17, v_inconsistent_4580_);
v___x_4595_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
lean_object* v___x_4597_; 
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 0, v___x_4595_);
v___x_4597_ = v___x_4570_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4595_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_mvarId_4568_);
v___x_4597_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4598_ = lean_st_ref_set(v_a_4555_, v___x_4597_);
v___x_4599_ = lean_array_fget(v_newFacts_4559_, v___x_4562_);
lean_dec(v___x_4562_);
lean_dec_ref(v_newFacts_4559_);
v___x_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4599_);
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
return v___x_4601_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4606_);
lean_dec(v_a_4606_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
lean_object* v___x_4620_; 
v___x_4620_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4609_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec(v_a_4621_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4633_, lean_object* v_rhs_4634_, lean_object* v_proof_4635_, uint8_t v_isHEq_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v___x_4648_; 
v___x_4648_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4633_, v_rhs_4634_, v_proof_4635_, v_isHEq_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v___x_4649_; 
lean_dec_ref_known(v___x_4648_, 1);
lean_inc(v_a_4646_);
lean_inc_ref(v_a_4645_);
lean_inc(v_a_4644_);
lean_inc_ref(v_a_4643_);
lean_inc(v_a_4642_);
lean_inc_ref(v_a_4641_);
lean_inc(v_a_4640_);
lean_inc_ref(v_a_4639_);
lean_inc(v_a_4638_);
lean_inc(v_a_4637_);
v___x_4649_ = lean_grind_process_new_facts(v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_);
return v___x_4649_;
}
else
{
return v___x_4648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4650_, lean_object* v_rhs_4651_, lean_object* v_proof_4652_, lean_object* v_isHEq_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
uint8_t v_isHEq_boxed_4665_; lean_object* v_res_4666_; 
v_isHEq_boxed_4665_ = lean_unbox(v_isHEq_4653_);
v_res_4666_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4650_, v_rhs_4651_, v_proof_4652_, v_isHEq_boxed_4665_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec_ref(v_a_4660_);
lean_dec(v_a_4659_);
lean_dec_ref(v_a_4658_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec(v_a_4654_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4667_, lean_object* v_rhs_4668_, lean_object* v_proof_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_){
_start:
{
uint8_t v___x_4681_; lean_object* v___x_4682_; 
v___x_4681_ = 0;
v___x_4682_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4667_, v_rhs_4668_, v_proof_4669_, v___x_4681_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4683_, lean_object* v_rhs_4684_, lean_object* v_proof_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4683_, v_rhs_4684_, v_proof_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
lean_dec(v_a_4689_);
lean_dec_ref(v_a_4688_);
lean_dec(v_a_4687_);
lean_dec(v_a_4686_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4698_, lean_object* v_rhs_4699_, lean_object* v_proof_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_){
_start:
{
uint8_t v___x_4712_; lean_object* v___x_4713_; 
v___x_4712_ = 1;
v___x_4713_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4698_, v_rhs_4699_, v_proof_4700_, v___x_4712_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4714_, lean_object* v_rhs_4715_, lean_object* v_proof_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4714_, v_rhs_4715_, v_proof_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_);
lean_dec(v_a_4726_);
lean_dec_ref(v_a_4725_);
lean_dec(v_a_4724_);
lean_dec_ref(v_a_4723_);
lean_dec(v_a_4722_);
lean_dec_ref(v_a_4721_);
lean_dec(v_a_4720_);
lean_dec_ref(v_a_4719_);
lean_dec(v_a_4718_);
lean_dec(v_a_4717_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v___x_4732_; lean_object* v_toGoalState_4733_; lean_object* v_mvarId_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4770_; 
v___x_4732_ = lean_st_ref_take(v_a_4730_);
v_toGoalState_4733_ = lean_ctor_get(v___x_4732_, 0);
v_mvarId_4734_ = lean_ctor_get(v___x_4732_, 1);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4736_ = v___x_4732_;
v_isShared_4737_ = v_isSharedCheck_4770_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_mvarId_4734_);
lean_inc(v_toGoalState_4733_);
lean_dec(v___x_4732_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4770_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v_nextDeclIdx_4738_; lean_object* v_enodeMap_4739_; lean_object* v_exprs_4740_; lean_object* v_parents_4741_; lean_object* v_congrTable_4742_; lean_object* v_appMap_4743_; lean_object* v_indicesFound_4744_; lean_object* v_newFacts_4745_; uint8_t v_inconsistent_4746_; lean_object* v_nextIdx_4747_; lean_object* v_newRawFacts_4748_; lean_object* v_facts_4749_; lean_object* v_extThms_4750_; lean_object* v_ematch_4751_; lean_object* v_inj_4752_; lean_object* v_split_4753_; lean_object* v_clean_4754_; lean_object* v_sstates_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4769_; 
v_nextDeclIdx_4738_ = lean_ctor_get(v_toGoalState_4733_, 0);
v_enodeMap_4739_ = lean_ctor_get(v_toGoalState_4733_, 1);
v_exprs_4740_ = lean_ctor_get(v_toGoalState_4733_, 2);
v_parents_4741_ = lean_ctor_get(v_toGoalState_4733_, 3);
v_congrTable_4742_ = lean_ctor_get(v_toGoalState_4733_, 4);
v_appMap_4743_ = lean_ctor_get(v_toGoalState_4733_, 5);
v_indicesFound_4744_ = lean_ctor_get(v_toGoalState_4733_, 6);
v_newFacts_4745_ = lean_ctor_get(v_toGoalState_4733_, 7);
v_inconsistent_4746_ = lean_ctor_get_uint8(v_toGoalState_4733_, sizeof(void*)*17);
v_nextIdx_4747_ = lean_ctor_get(v_toGoalState_4733_, 8);
v_newRawFacts_4748_ = lean_ctor_get(v_toGoalState_4733_, 9);
v_facts_4749_ = lean_ctor_get(v_toGoalState_4733_, 10);
v_extThms_4750_ = lean_ctor_get(v_toGoalState_4733_, 11);
v_ematch_4751_ = lean_ctor_get(v_toGoalState_4733_, 12);
v_inj_4752_ = lean_ctor_get(v_toGoalState_4733_, 13);
v_split_4753_ = lean_ctor_get(v_toGoalState_4733_, 14);
v_clean_4754_ = lean_ctor_get(v_toGoalState_4733_, 15);
v_sstates_4755_ = lean_ctor_get(v_toGoalState_4733_, 16);
v_isSharedCheck_4769_ = !lean_is_exclusive(v_toGoalState_4733_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4757_ = v_toGoalState_4733_;
v_isShared_4758_ = v_isSharedCheck_4769_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_sstates_4755_);
lean_inc(v_clean_4754_);
lean_inc(v_split_4753_);
lean_inc(v_inj_4752_);
lean_inc(v_ematch_4751_);
lean_inc(v_extThms_4750_);
lean_inc(v_facts_4749_);
lean_inc(v_newRawFacts_4748_);
lean_inc(v_nextIdx_4747_);
lean_inc(v_newFacts_4745_);
lean_inc(v_indicesFound_4744_);
lean_inc(v_appMap_4743_);
lean_inc(v_congrTable_4742_);
lean_inc(v_parents_4741_);
lean_inc(v_exprs_4740_);
lean_inc(v_enodeMap_4739_);
lean_inc(v_nextDeclIdx_4738_);
lean_dec(v_toGoalState_4733_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4769_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4759_; lean_object* v___x_4761_; 
v___x_4759_ = l_Lean_PersistentArray_push___redArg(v_facts_4749_, v_fact_4729_);
if (v_isShared_4758_ == 0)
{
lean_ctor_set(v___x_4757_, 10, v___x_4759_);
v___x_4761_ = v___x_4757_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_nextDeclIdx_4738_);
lean_ctor_set(v_reuseFailAlloc_4768_, 1, v_enodeMap_4739_);
lean_ctor_set(v_reuseFailAlloc_4768_, 2, v_exprs_4740_);
lean_ctor_set(v_reuseFailAlloc_4768_, 3, v_parents_4741_);
lean_ctor_set(v_reuseFailAlloc_4768_, 4, v_congrTable_4742_);
lean_ctor_set(v_reuseFailAlloc_4768_, 5, v_appMap_4743_);
lean_ctor_set(v_reuseFailAlloc_4768_, 6, v_indicesFound_4744_);
lean_ctor_set(v_reuseFailAlloc_4768_, 7, v_newFacts_4745_);
lean_ctor_set(v_reuseFailAlloc_4768_, 8, v_nextIdx_4747_);
lean_ctor_set(v_reuseFailAlloc_4768_, 9, v_newRawFacts_4748_);
lean_ctor_set(v_reuseFailAlloc_4768_, 10, v___x_4759_);
lean_ctor_set(v_reuseFailAlloc_4768_, 11, v_extThms_4750_);
lean_ctor_set(v_reuseFailAlloc_4768_, 12, v_ematch_4751_);
lean_ctor_set(v_reuseFailAlloc_4768_, 13, v_inj_4752_);
lean_ctor_set(v_reuseFailAlloc_4768_, 14, v_split_4753_);
lean_ctor_set(v_reuseFailAlloc_4768_, 15, v_clean_4754_);
lean_ctor_set(v_reuseFailAlloc_4768_, 16, v_sstates_4755_);
lean_ctor_set_uint8(v_reuseFailAlloc_4768_, sizeof(void*)*17, v_inconsistent_4746_);
v___x_4761_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
lean_object* v___x_4763_; 
if (v_isShared_4737_ == 0)
{
lean_ctor_set(v___x_4736_, 0, v___x_4761_);
v___x_4763_ = v___x_4736_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4761_);
lean_ctor_set(v_reuseFailAlloc_4767_, 1, v_mvarId_4734_);
v___x_4763_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4764_ = lean_st_ref_set(v_a_4730_, v___x_4763_);
v___x_4765_ = lean_box(0);
v___x_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
return v___x_4766_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4771_, v_a_4772_);
lean_dec(v_a_4772_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v___x_4787_; 
v___x_4787_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4775_, v_a_4776_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4788_, v_a_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
lean_dec(v_a_4796_);
lean_dec_ref(v_a_4795_);
lean_dec(v_a_4794_);
lean_dec_ref(v_a_4793_);
lean_dec(v_a_4792_);
lean_dec_ref(v_a_4791_);
lean_dec(v_a_4790_);
lean_dec(v_a_4789_);
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4801_, lean_object* v_rhs_4802_, lean_object* v_proof_4803_, lean_object* v_generation_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_){
_start:
{
lean_object* v___x_4816_; 
lean_inc_ref(v_rhs_4802_);
lean_inc_ref(v_lhs_4801_);
v___x_4816_ = l_Lean_Meta_mkEq(v_lhs_4801_, v_rhs_4802_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v_a_4817_; lean_object* v___x_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4828_; 
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
lean_inc_n(v_a_4817_, 2);
lean_dec_ref_known(v___x_4816_, 1);
v___x_4818_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4817_, v_a_4805_);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_4828_ == 0)
{
lean_object* v_unused_4829_; 
v_unused_4829_ = lean_ctor_get(v___x_4818_, 0);
lean_dec(v_unused_4829_);
v___x_4820_ = v___x_4818_;
v_isShared_4821_ = v_isSharedCheck_4828_;
goto v_resetjp_4819_;
}
else
{
lean_dec(v___x_4818_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4828_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
lean_ctor_set_tag(v___x_4820_, 1);
lean_ctor_set(v___x_4820_, 0, v_a_4817_);
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4817_);
v___x_4823_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
lean_object* v___x_4824_; 
lean_inc(v_a_4814_);
lean_inc_ref(v_a_4813_);
lean_inc(v_a_4812_);
lean_inc_ref(v_a_4811_);
lean_inc(v_a_4810_);
lean_inc_ref(v_a_4809_);
lean_inc(v_a_4808_);
lean_inc_ref(v_a_4807_);
lean_inc(v_a_4806_);
lean_inc(v_a_4805_);
lean_inc_ref(v___x_4823_);
lean_inc(v_generation_4804_);
lean_inc_ref(v_lhs_4801_);
v___x_4824_ = lean_grind_internalize(v_lhs_4801_, v_generation_4804_, v___x_4823_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v___x_4825_; 
lean_dec_ref_known(v___x_4824_, 1);
lean_inc(v_a_4814_);
lean_inc_ref(v_a_4813_);
lean_inc(v_a_4812_);
lean_inc_ref(v_a_4811_);
lean_inc(v_a_4810_);
lean_inc_ref(v_a_4809_);
lean_inc(v_a_4808_);
lean_inc_ref(v_a_4807_);
lean_inc(v_a_4806_);
lean_inc(v_a_4805_);
lean_inc_ref(v_rhs_4802_);
v___x_4825_ = lean_grind_internalize(v_rhs_4802_, v_generation_4804_, v___x_4823_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_object* v___x_4826_; 
lean_dec_ref_known(v___x_4825_, 1);
v___x_4826_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4801_, v_rhs_4802_, v_proof_4803_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
return v___x_4826_;
}
else
{
lean_dec_ref(v_proof_4803_);
lean_dec_ref(v_rhs_4802_);
lean_dec_ref(v_lhs_4801_);
return v___x_4825_;
}
}
else
{
lean_dec_ref(v___x_4823_);
lean_dec(v_generation_4804_);
lean_dec_ref(v_proof_4803_);
lean_dec_ref(v_rhs_4802_);
lean_dec_ref(v_lhs_4801_);
return v___x_4824_;
}
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
lean_dec(v_generation_4804_);
lean_dec_ref(v_proof_4803_);
lean_dec_ref(v_rhs_4802_);
lean_dec_ref(v_lhs_4801_);
v_a_4830_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4816_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4816_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4835_; 
if (v_isShared_4833_ == 0)
{
v___x_4835_ = v___x_4832_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4838_, lean_object* v_rhs_4839_, lean_object* v_proof_4840_, lean_object* v_generation_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_){
_start:
{
lean_object* v_res_4853_; 
v_res_4853_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4838_, v_rhs_4839_, v_proof_4840_, v_generation_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_a_4846_);
lean_dec(v_a_4845_);
lean_dec_ref(v_a_4844_);
lean_dec(v_a_4843_);
lean_dec(v_a_4842_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4854_, lean_object* v_generation_4855_, lean_object* v_p_4856_, uint8_t v_isNeg_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = lean_box(0);
lean_inc(v_a_4867_);
lean_inc_ref(v_a_4866_);
lean_inc(v_a_4865_);
lean_inc_ref(v_a_4864_);
lean_inc(v_a_4863_);
lean_inc_ref(v_a_4862_);
lean_inc(v_a_4861_);
lean_inc_ref(v_a_4860_);
lean_inc(v_a_4859_);
lean_inc(v_a_4858_);
lean_inc_ref(v_p_4856_);
v___x_4870_ = lean_grind_internalize(v_p_4856_, v_generation_4855_, v___x_4869_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_dec_ref_known(v___x_4870_, 1);
if (v_isNeg_4857_ == 0)
{
lean_object* v___x_4871_; 
v___x_4871_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4862_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4872_; lean_object* v___x_4873_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
lean_inc(v_a_4872_);
lean_dec_ref_known(v___x_4871_, 1);
v___x_4873_ = l_Lean_Meta_mkEqTrue(v_proof_4854_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4875_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref_known(v___x_4873_, 1);
v___x_4875_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4856_, v_a_4872_, v_a_4874_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
return v___x_4875_;
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
lean_dec(v_a_4872_);
lean_dec_ref(v_p_4856_);
v_a_4876_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4873_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4873_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4879_ == 0)
{
v___x_4881_ = v___x_4878_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4876_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
lean_dec_ref(v_p_4856_);
lean_dec_ref(v_proof_4854_);
v_a_4884_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4871_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4871_);
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
lean_object* v___x_4892_; 
v___x_4892_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4862_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v___x_4894_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4893_);
lean_dec_ref_known(v___x_4892_, 1);
v___x_4894_ = l_Lean_Meta_mkEqFalse(v_proof_4854_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
if (lean_obj_tag(v___x_4894_) == 0)
{
lean_object* v_a_4895_; lean_object* v___x_4896_; 
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
lean_inc(v_a_4895_);
lean_dec_ref_known(v___x_4894_, 1);
v___x_4896_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4856_, v_a_4893_, v_a_4895_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
return v___x_4896_;
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
lean_dec(v_a_4893_);
lean_dec_ref(v_p_4856_);
v_a_4897_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4894_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4894_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
lean_dec_ref(v_p_4856_);
lean_dec_ref(v_proof_4854_);
v_a_4905_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4892_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4892_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4856_);
lean_dec_ref(v_proof_4854_);
return v___x_4870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4913_, lean_object* v_generation_4914_, lean_object* v_p_4915_, lean_object* v_isNeg_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
uint8_t v_isNeg_boxed_4928_; lean_object* v_res_4929_; 
v_isNeg_boxed_4928_ = lean_unbox(v_isNeg_4916_);
v_res_4929_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4913_, v_generation_4914_, v_p_4915_, v_isNeg_boxed_4928_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
lean_dec(v_a_4924_);
lean_dec_ref(v_a_4923_);
lean_dec(v_a_4922_);
lean_dec_ref(v_a_4921_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_a_4918_);
lean_dec(v_a_4917_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4930_, lean_object* v_generation_4931_, lean_object* v_p_4932_, lean_object* v_lhs_4933_, lean_object* v_rhs_4934_, uint8_t v_isNeg_4935_, uint8_t v_isHEq_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_){
_start:
{
if (v_isNeg_4935_ == 0)
{
lean_object* v___x_4948_; lean_object* v___x_4949_; 
lean_inc_ref(v_p_4932_);
v___x_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4948_, 0, v_p_4932_);
lean_inc(v_a_4946_);
lean_inc_ref(v_a_4945_);
lean_inc(v_a_4944_);
lean_inc_ref(v_a_4943_);
lean_inc(v_a_4942_);
lean_inc_ref(v_a_4941_);
lean_inc(v_a_4940_);
lean_inc_ref(v_a_4939_);
lean_inc(v_a_4938_);
lean_inc(v_a_4937_);
lean_inc_ref(v___x_4948_);
lean_inc(v_generation_4931_);
lean_inc_ref(v_lhs_4933_);
v___x_4949_ = lean_grind_internalize(v_lhs_4933_, v_generation_4931_, v___x_4948_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v___x_4950_; 
lean_dec_ref_known(v___x_4949_, 1);
lean_inc(v_a_4946_);
lean_inc_ref(v_a_4945_);
lean_inc(v_a_4944_);
lean_inc_ref(v_a_4943_);
lean_inc(v_a_4942_);
lean_inc_ref(v_a_4941_);
lean_inc(v_a_4940_);
lean_inc_ref(v_a_4939_);
lean_inc(v_a_4938_);
lean_inc(v_a_4937_);
lean_inc_ref(v_rhs_4934_);
v___x_4950_ = lean_grind_internalize(v_rhs_4934_, v_generation_4931_, v___x_4948_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v___x_4951_; lean_object* v___x_4952_; 
lean_dec_ref_known(v___x_4950_, 1);
v___x_4951_ = lean_box(0);
v___x_4952_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4932_, v___x_4951_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v___x_4953_; 
lean_dec_ref_known(v___x_4952_, 1);
v___x_4953_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4933_, v_rhs_4934_, v_proof_4930_, v_isHEq_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
return v___x_4953_;
}
else
{
lean_dec_ref(v_rhs_4934_);
lean_dec_ref(v_lhs_4933_);
lean_dec_ref(v_proof_4930_);
return v___x_4952_;
}
}
else
{
lean_dec_ref(v_rhs_4934_);
lean_dec_ref(v_lhs_4933_);
lean_dec_ref(v_p_4932_);
lean_dec_ref(v_proof_4930_);
return v___x_4950_;
}
}
else
{
lean_dec_ref_known(v___x_4948_, 1);
lean_dec_ref(v_rhs_4934_);
lean_dec_ref(v_lhs_4933_);
lean_dec_ref(v_p_4932_);
lean_dec(v_generation_4931_);
lean_dec_ref(v_proof_4930_);
return v___x_4949_;
}
}
else
{
lean_object* v___x_4954_; lean_object* v___x_4955_; 
lean_dec_ref(v_rhs_4934_);
lean_dec_ref(v_lhs_4933_);
v___x_4954_ = lean_box(0);
lean_inc(v_a_4946_);
lean_inc_ref(v_a_4945_);
lean_inc(v_a_4944_);
lean_inc_ref(v_a_4943_);
lean_inc(v_a_4942_);
lean_inc_ref(v_a_4941_);
lean_inc(v_a_4940_);
lean_inc_ref(v_a_4939_);
lean_inc(v_a_4938_);
lean_inc(v_a_4937_);
lean_inc_ref(v_p_4932_);
v___x_4955_ = lean_grind_internalize(v_p_4932_, v_generation_4931_, v___x_4954_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v___x_4956_; 
lean_dec_ref_known(v___x_4955_, 1);
v___x_4956_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4941_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_object* v_a_4957_; lean_object* v___x_4958_; 
v_a_4957_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_a_4957_);
lean_dec_ref_known(v___x_4956_, 1);
v___x_4958_ = l_Lean_Meta_mkEqFalse(v_proof_4930_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4960_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref_known(v___x_4958_, 1);
v___x_4960_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4932_, v_a_4957_, v_a_4959_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
return v___x_4960_;
}
else
{
lean_object* v_a_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4968_; 
lean_dec(v_a_4957_);
lean_dec_ref(v_p_4932_);
v_a_4961_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4963_ = v___x_4958_;
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_a_4961_);
lean_dec(v___x_4958_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4966_; 
if (v_isShared_4964_ == 0)
{
v___x_4966_ = v___x_4963_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
else
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_dec_ref(v_p_4932_);
lean_dec_ref(v_proof_4930_);
v_a_4969_ = lean_ctor_get(v___x_4956_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4956_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4956_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4956_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
else
{
lean_dec_ref(v_p_4932_);
lean_dec_ref(v_proof_4930_);
return v___x_4955_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4977_ = _args[0];
lean_object* v_generation_4978_ = _args[1];
lean_object* v_p_4979_ = _args[2];
lean_object* v_lhs_4980_ = _args[3];
lean_object* v_rhs_4981_ = _args[4];
lean_object* v_isNeg_4982_ = _args[5];
lean_object* v_isHEq_4983_ = _args[6];
lean_object* v_a_4984_ = _args[7];
lean_object* v_a_4985_ = _args[8];
lean_object* v_a_4986_ = _args[9];
lean_object* v_a_4987_ = _args[10];
lean_object* v_a_4988_ = _args[11];
lean_object* v_a_4989_ = _args[12];
lean_object* v_a_4990_ = _args[13];
lean_object* v_a_4991_ = _args[14];
lean_object* v_a_4992_ = _args[15];
lean_object* v_a_4993_ = _args[16];
lean_object* v_a_4994_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4995_; uint8_t v_isHEq_boxed_4996_; lean_object* v_res_4997_; 
v_isNeg_boxed_4995_ = lean_unbox(v_isNeg_4982_);
v_isHEq_boxed_4996_ = lean_unbox(v_isHEq_4983_);
v_res_4997_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4977_, v_generation_4978_, v_p_4979_, v_lhs_4980_, v_rhs_4981_, v_isNeg_boxed_4995_, v_isHEq_boxed_4996_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
lean_dec(v_a_4989_);
lean_dec_ref(v_a_4988_);
lean_dec(v_a_4987_);
lean_dec_ref(v_a_4986_);
lean_dec(v_a_4985_);
lean_dec(v_a_4984_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_5001_, lean_object* v_generation_5002_, lean_object* v_p_5003_, uint8_t v_isNeg_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v___x_5016_; 
lean_inc_ref(v_p_5003_);
v___x_5016_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_5003_, v_a_5012_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v_a_5017_; lean_object* v___x_5018_; uint8_t v___x_5019_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5017_);
lean_dec_ref_known(v___x_5016_, 1);
v___x_5018_ = l_Lean_Expr_cleanupAnnotations(v_a_5017_);
v___x_5019_ = l_Lean_Expr_isApp(v___x_5018_);
if (v___x_5019_ == 0)
{
lean_object* v___x_5020_; 
lean_dec_ref(v___x_5018_);
v___x_5020_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5001_, v_generation_5002_, v_p_5003_, v_isNeg_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
return v___x_5020_;
}
else
{
lean_object* v_arg_5021_; lean_object* v___x_5022_; uint8_t v___x_5023_; 
v_arg_5021_ = lean_ctor_get(v___x_5018_, 1);
lean_inc_ref(v_arg_5021_);
v___x_5022_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5018_);
v___x_5023_ = l_Lean_Expr_isApp(v___x_5022_);
if (v___x_5023_ == 0)
{
lean_object* v___x_5024_; 
lean_dec_ref(v___x_5022_);
lean_dec_ref(v_arg_5021_);
v___x_5024_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5001_, v_generation_5002_, v_p_5003_, v_isNeg_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
return v___x_5024_;
}
else
{
lean_object* v_arg_5025_; lean_object* v___x_5026_; uint8_t v___x_5027_; 
v_arg_5025_ = lean_ctor_get(v___x_5022_, 1);
lean_inc_ref(v_arg_5025_);
v___x_5026_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5022_);
v___x_5027_ = l_Lean_Expr_isApp(v___x_5026_);
if (v___x_5027_ == 0)
{
lean_object* v___x_5028_; 
lean_dec_ref(v___x_5026_);
lean_dec_ref(v_arg_5025_);
lean_dec_ref(v_arg_5021_);
v___x_5028_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5001_, v_generation_5002_, v_p_5003_, v_isNeg_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
return v___x_5028_;
}
else
{
lean_object* v_arg_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; uint8_t v___x_5032_; 
v_arg_5029_ = lean_ctor_get(v___x_5026_, 1);
lean_inc_ref(v_arg_5029_);
v___x_5030_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5026_);
v___x_5031_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5032_ = l_Lean_Expr_isConstOf(v___x_5030_, v___x_5031_);
if (v___x_5032_ == 0)
{
uint8_t v___x_5033_; 
lean_dec_ref(v_arg_5025_);
v___x_5033_ = l_Lean_Expr_isApp(v___x_5030_);
if (v___x_5033_ == 0)
{
lean_object* v___x_5034_; 
lean_dec_ref(v___x_5030_);
lean_dec_ref(v_arg_5029_);
lean_dec_ref(v_arg_5021_);
v___x_5034_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5001_, v_generation_5002_, v_p_5003_, v_isNeg_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
return v___x_5034_;
}
else
{
lean_object* v___x_5035_; lean_object* v___x_5036_; uint8_t v___x_5037_; 
v___x_5035_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5030_);
v___x_5036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5037_ = l_Lean_Expr_isConstOf(v___x_5035_, v___x_5036_);
lean_dec_ref(v___x_5035_);
if (v___x_5037_ == 0)
{
lean_object* v___x_5038_; 
lean_dec_ref(v_arg_5029_);
lean_dec_ref(v_arg_5021_);
v___x_5038_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5001_, v_generation_5002_, v_p_5003_, v_isNeg_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
return v___x_5038_;
}
else
{
lean_object* v___x_5039_; 
v___x_5039_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_5001_, v_generation_5002_, v_p_5003_, v_arg_5029_, v_arg_5021_, v_isNeg_5004_, v___x_5037_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
return v___x_5039_;
}
}
}
else
{
uint8_t v___x_5040_; 
lean_dec_ref(v___x_5030_);
v___x_5040_ = l_Lean_Expr_isProp(v_arg_5029_);
lean_dec_ref(v_arg_5029_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; 
v___x_5041_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_5001_, v_generation_5002_, v_p_5003_, v_arg_5025_, v_arg_5021_, v_isNeg_5004_, v___x_5040_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
return v___x_5041_;
}
else
{
lean_object* v___x_5042_; 
lean_dec_ref(v_arg_5025_);
lean_dec_ref(v_arg_5021_);
v___x_5042_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_5001_, v_generation_5002_, v_p_5003_, v_isNeg_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
return v___x_5042_;
}
}
}
}
}
}
else
{
lean_object* v_a_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5050_; 
lean_dec_ref(v_p_5003_);
lean_dec(v_generation_5002_);
lean_dec_ref(v_proof_5001_);
v_a_5043_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_5045_ = v___x_5016_;
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_a_5043_);
lean_dec(v___x_5016_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5048_; 
if (v_isShared_5046_ == 0)
{
v___x_5048_ = v___x_5045_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5043_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5051_, lean_object* v_generation_5052_, lean_object* v_p_5053_, lean_object* v_isNeg_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_){
_start:
{
uint8_t v_isNeg_boxed_5066_; lean_object* v_res_5067_; 
v_isNeg_boxed_5066_ = lean_unbox(v_isNeg_5054_);
v_res_5067_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5051_, v_generation_5052_, v_p_5053_, v_isNeg_boxed_5066_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
lean_dec(v_a_5062_);
lean_dec_ref(v_a_5061_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
lean_dec(v_a_5058_);
lean_dec_ref(v_a_5057_);
lean_dec(v_a_5056_);
lean_dec(v_a_5055_);
return v_res_5067_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5076_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5077_ = l_Lean_Name_append(v___x_5076_, v___x_5075_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5078_, lean_object* v_proof_5079_, lean_object* v_generation_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_){
_start:
{
lean_object* v___y_5093_; lean_object* v___y_5094_; lean_object* v___y_5095_; lean_object* v___y_5096_; lean_object* v___y_5097_; lean_object* v___y_5098_; lean_object* v___y_5099_; lean_object* v___y_5100_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___y_5106_; lean_object* v___y_5107_; lean_object* v___y_5108_; lean_object* v___y_5109_; lean_object* v___y_5110_; lean_object* v___y_5111_; lean_object* v___y_5112_; lean_object* v___y_5113_; lean_object* v___y_5114_; lean_object* v___y_5115_; lean_object* v___x_5123_; lean_object* v_options_5124_; uint8_t v_hasTrace_5125_; 
lean_inc_ref(v_fact_5078_);
v___x_5123_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5078_, v_a_5081_);
lean_dec_ref(v___x_5123_);
v_options_5124_ = lean_ctor_get(v_a_5089_, 2);
v_hasTrace_5125_ = lean_ctor_get_uint8(v_options_5124_, sizeof(void*)*1);
if (v_hasTrace_5125_ == 0)
{
v___y_5106_ = v_a_5081_;
v___y_5107_ = v_a_5082_;
v___y_5108_ = v_a_5083_;
v___y_5109_ = v_a_5084_;
v___y_5110_ = v_a_5085_;
v___y_5111_ = v_a_5086_;
v___y_5112_ = v_a_5087_;
v___y_5113_ = v_a_5088_;
v___y_5114_ = v_a_5089_;
v___y_5115_ = v_a_5090_;
goto v___jp_5105_;
}
else
{
lean_object* v_inheritedTraceOptions_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; uint8_t v___x_5129_; 
v_inheritedTraceOptions_5126_ = lean_ctor_get(v_a_5089_, 13);
v___x_5127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5129_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5126_, v_options_5124_, v___x_5128_);
if (v___x_5129_ == 0)
{
v___y_5106_ = v_a_5081_;
v___y_5107_ = v_a_5082_;
v___y_5108_ = v_a_5083_;
v___y_5109_ = v_a_5084_;
v___y_5110_ = v_a_5085_;
v___y_5111_ = v_a_5086_;
v___y_5112_ = v_a_5087_;
v___y_5113_ = v_a_5088_;
v___y_5114_ = v_a_5089_;
v___y_5115_ = v_a_5090_;
goto v___jp_5105_;
}
else
{
lean_object* v___x_5130_; 
v___x_5130_ = l_Lean_Meta_Grind_updateLastTag(v_a_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v___x_5131_; lean_object* v___x_5132_; 
lean_dec_ref_known(v___x_5130_, 1);
lean_inc_ref(v_fact_5078_);
v___x_5131_ = l_Lean_MessageData_ofExpr(v_fact_5078_);
v___x_5132_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5127_, v___x_5131_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_dec_ref_known(v___x_5132_, 1);
v___y_5106_ = v_a_5081_;
v___y_5107_ = v_a_5082_;
v___y_5108_ = v_a_5083_;
v___y_5109_ = v_a_5084_;
v___y_5110_ = v_a_5085_;
v___y_5111_ = v_a_5086_;
v___y_5112_ = v_a_5087_;
v___y_5113_ = v_a_5088_;
v___y_5114_ = v_a_5089_;
v___y_5115_ = v_a_5090_;
goto v___jp_5105_;
}
else
{
lean_dec(v_generation_5080_);
lean_dec_ref(v_proof_5079_);
lean_dec_ref(v_fact_5078_);
return v___x_5132_;
}
}
else
{
lean_dec(v_generation_5080_);
lean_dec_ref(v_proof_5079_);
lean_dec_ref(v_fact_5078_);
return v___x_5130_;
}
}
}
v___jp_5092_:
{
uint8_t v___x_5103_; lean_object* v___x_5104_; 
v___x_5103_ = 0;
v___x_5104_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5079_, v_generation_5080_, v_fact_5078_, v___x_5103_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
return v___x_5104_;
}
v___jp_5105_:
{
lean_object* v___x_5116_; uint8_t v___x_5117_; 
lean_inc_ref(v_fact_5078_);
v___x_5116_ = l_Lean_Expr_cleanupAnnotations(v_fact_5078_);
v___x_5117_ = l_Lean_Expr_isApp(v___x_5116_);
if (v___x_5117_ == 0)
{
lean_dec_ref(v___x_5116_);
v___y_5093_ = v___y_5106_;
v___y_5094_ = v___y_5107_;
v___y_5095_ = v___y_5108_;
v___y_5096_ = v___y_5109_;
v___y_5097_ = v___y_5110_;
v___y_5098_ = v___y_5111_;
v___y_5099_ = v___y_5112_;
v___y_5100_ = v___y_5113_;
v___y_5101_ = v___y_5114_;
v___y_5102_ = v___y_5115_;
goto v___jp_5092_;
}
else
{
lean_object* v_arg_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; uint8_t v___x_5121_; 
v_arg_5118_ = lean_ctor_get(v___x_5116_, 1);
lean_inc_ref(v_arg_5118_);
v___x_5119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5116_);
v___x_5120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5121_ = l_Lean_Expr_isConstOf(v___x_5119_, v___x_5120_);
lean_dec_ref(v___x_5119_);
if (v___x_5121_ == 0)
{
lean_dec_ref(v_arg_5118_);
v___y_5093_ = v___y_5106_;
v___y_5094_ = v___y_5107_;
v___y_5095_ = v___y_5108_;
v___y_5096_ = v___y_5109_;
v___y_5097_ = v___y_5110_;
v___y_5098_ = v___y_5111_;
v___y_5099_ = v___y_5112_;
v___y_5100_ = v___y_5113_;
v___y_5101_ = v___y_5114_;
v___y_5102_ = v___y_5115_;
goto v___jp_5092_;
}
else
{
lean_object* v___x_5122_; 
lean_dec_ref(v_fact_5078_);
v___x_5122_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5079_, v_generation_5080_, v_arg_5118_, v___x_5121_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_);
return v___x_5122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5133_, lean_object* v_proof_5134_, lean_object* v_generation_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_){
_start:
{
lean_object* v_res_5147_; 
v_res_5147_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5133_, v_proof_5134_, v_generation_5135_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_);
lean_dec(v_a_5145_);
lean_dec_ref(v_a_5144_);
lean_dec(v_a_5143_);
lean_dec_ref(v_a_5142_);
lean_dec(v_a_5141_);
lean_dec_ref(v_a_5140_);
lean_dec(v_a_5139_);
lean_dec_ref(v_a_5138_);
lean_dec(v_a_5137_);
lean_dec(v_a_5136_);
return v_res_5147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
lean_object* v___x_5162_; 
v___x_5162_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5151_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_a_5163_; uint8_t v___x_5164_; 
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_a_5163_);
lean_dec_ref_known(v___x_5162_, 1);
v___x_5164_ = lean_unbox(v_a_5163_);
lean_dec(v_a_5163_);
if (v___x_5164_ == 0)
{
lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5165_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5166_ = l_Lean_Core_checkSystem(v___x_5165_, v___y_5159_, v___y_5160_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v___x_5167_; 
lean_dec_ref_known(v___x_5166_, 1);
v___x_5167_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5151_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5204_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5170_ = v___x_5167_;
v_isShared_5171_ = v_isSharedCheck_5204_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_5167_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5204_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
if (lean_obj_tag(v_a_5168_) == 1)
{
lean_object* v_val_5172_; 
lean_del_object(v___x_5170_);
v_val_5172_ = lean_ctor_get(v_a_5168_, 0);
lean_inc(v_val_5172_);
lean_dec_ref_known(v_a_5168_, 1);
if (lean_obj_tag(v_val_5172_) == 0)
{
lean_object* v_lhs_5173_; lean_object* v_rhs_5174_; lean_object* v_proof_5175_; uint8_t v_isHEq_5176_; lean_object* v___x_5177_; 
v_lhs_5173_ = lean_ctor_get(v_val_5172_, 0);
lean_inc_ref(v_lhs_5173_);
v_rhs_5174_ = lean_ctor_get(v_val_5172_, 1);
lean_inc_ref(v_rhs_5174_);
v_proof_5175_ = lean_ctor_get(v_val_5172_, 2);
lean_inc_ref(v_proof_5175_);
v_isHEq_5176_ = lean_ctor_get_uint8(v_val_5172_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5172_, 3);
v___x_5177_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5173_, v_rhs_5174_, v_proof_5175_, v_isHEq_5176_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
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
else
{
lean_object* v_prop_5187_; lean_object* v_proof_5188_; lean_object* v_generation_5189_; lean_object* v___x_5190_; 
v_prop_5187_ = lean_ctor_get(v_val_5172_, 0);
lean_inc_ref(v_prop_5187_);
v_proof_5188_ = lean_ctor_get(v_val_5172_, 1);
lean_inc_ref(v_proof_5188_);
v_generation_5189_ = lean_ctor_get(v_val_5172_, 2);
lean_inc(v_generation_5189_);
lean_dec_ref_known(v_val_5172_, 3);
v___x_5190_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5187_, v_proof_5188_, v_generation_5189_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_dec_ref_known(v___x_5190_, 1);
goto _start;
}
else
{
lean_object* v_a_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5199_; 
v_a_5192_ = lean_ctor_get(v___x_5190_, 0);
v_isSharedCheck_5199_ = !lean_is_exclusive(v___x_5190_);
if (v_isSharedCheck_5199_ == 0)
{
v___x_5194_ = v___x_5190_;
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_a_5192_);
lean_dec(v___x_5190_);
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
}
else
{
lean_object* v___x_5200_; lean_object* v___x_5202_; 
lean_dec(v_a_5168_);
v___x_5200_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5171_ == 0)
{
lean_ctor_set(v___x_5170_, 0, v___x_5200_);
v___x_5202_ = v___x_5170_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5200_);
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
else
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
v_a_5205_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5167_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5167_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5210_; 
if (v_isShared_5208_ == 0)
{
v___x_5210_ = v___x_5207_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5205_);
v___x_5210_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
return v___x_5210_;
}
}
}
}
else
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
v_a_5213_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5166_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5166_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
if (v_isShared_5216_ == 0)
{
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
else
{
lean_object* v___x_5221_; 
v___x_5221_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5151_);
if (lean_obj_tag(v___x_5221_) == 0)
{
lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5229_; 
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5229_ == 0)
{
lean_object* v_unused_5230_; 
v_unused_5230_ = lean_ctor_get(v___x_5221_, 0);
lean_dec(v_unused_5230_);
v___x_5223_ = v___x_5221_;
v_isShared_5224_ = v_isSharedCheck_5229_;
goto v_resetjp_5222_;
}
else
{
lean_dec(v___x_5221_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5229_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5225_; lean_object* v___x_5227_; 
v___x_5225_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5224_ == 0)
{
lean_ctor_set(v___x_5223_, 0, v___x_5225_);
v___x_5227_ = v___x_5223_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v___x_5225_);
v___x_5227_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
return v___x_5227_;
}
}
}
else
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5238_; 
v_a_5231_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5233_ = v___x_5221_;
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5221_);
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
}
else
{
lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5246_; 
v_a_5239_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5241_ = v___x_5162_;
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5162_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec(v___y_5247_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_){
_start:
{
lean_object* v___x_5270_; 
v___x_5270_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5259_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_);
lean_dec(v_a_5268_);
lean_dec_ref(v_a_5267_);
lean_dec(v_a_5266_);
lean_dec_ref(v_a_5265_);
lean_dec(v_a_5264_);
lean_dec_ref(v_a_5263_);
lean_dec(v_a_5262_);
lean_dec_ref(v_a_5261_);
lean_dec(v_a_5260_);
lean_dec(v_a_5259_);
if (lean_obj_tag(v___x_5270_) == 0)
{
lean_object* v_a_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5284_; 
v_a_5271_ = lean_ctor_get(v___x_5270_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5270_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5273_ = v___x_5270_;
v_isShared_5274_ = v_isSharedCheck_5284_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_a_5271_);
lean_dec(v___x_5270_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5284_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v_fst_5275_; 
v_fst_5275_ = lean_ctor_get(v_a_5271_, 0);
lean_inc(v_fst_5275_);
lean_dec(v_a_5271_);
if (lean_obj_tag(v_fst_5275_) == 0)
{
lean_object* v___x_5276_; lean_object* v___x_5278_; 
v___x_5276_ = lean_box(0);
if (v_isShared_5274_ == 0)
{
lean_ctor_set(v___x_5273_, 0, v___x_5276_);
v___x_5278_ = v___x_5273_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5276_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
else
{
lean_object* v_val_5280_; lean_object* v___x_5282_; 
v_val_5280_ = lean_ctor_get(v_fst_5275_, 0);
lean_inc(v_val_5280_);
lean_dec_ref_known(v_fst_5275_, 1);
if (v_isShared_5274_ == 0)
{
lean_ctor_set(v___x_5273_, 0, v_val_5280_);
v___x_5282_ = v___x_5273_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_val_5280_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
v_a_5285_ = lean_ctor_get(v___x_5270_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5270_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___x_5270_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5270_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5288_ == 0)
{
v___x_5290_ = v___x_5287_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_){
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = lean_grind_process_new_facts(v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_inst_5305_, lean_object* v_a_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_){
_start:
{
lean_object* v___x_5318_; 
v___x_5318_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_inst_5319_, lean_object* v_a_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_inst_5319_, v_a_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v___y_5322_);
lean_dec(v___y_5321_);
lean_dec_ref(v_a_5320_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5333_, lean_object* v_proof_5334_, lean_object* v_generation_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_){
_start:
{
uint8_t v___x_5347_; 
lean_inc_ref(v_fact_5333_);
v___x_5347_ = l_Lean_Expr_isTrue(v_fact_5333_);
if (v___x_5347_ == 0)
{
lean_object* v___x_5348_; 
v___x_5348_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5336_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5360_; 
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5351_ = v___x_5348_;
v_isShared_5352_ = v_isSharedCheck_5360_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5348_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5360_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
uint8_t v___x_5353_; 
v___x_5353_ = lean_unbox(v_a_5349_);
lean_dec(v_a_5349_);
if (v___x_5353_ == 0)
{
lean_object* v___x_5354_; lean_object* v___x_5355_; 
lean_del_object(v___x_5351_);
v___x_5354_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5336_);
lean_dec_ref(v___x_5354_);
v___x_5355_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5333_, v_proof_5334_, v_generation_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_, v_a_5342_, v_a_5343_, v_a_5344_, v_a_5345_);
return v___x_5355_;
}
else
{
lean_object* v___x_5356_; lean_object* v___x_5358_; 
lean_dec(v_generation_5335_);
lean_dec_ref(v_proof_5334_);
lean_dec_ref(v_fact_5333_);
v___x_5356_ = lean_box(0);
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 0, v___x_5356_);
v___x_5358_ = v___x_5351_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5356_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
}
}
else
{
lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5368_; 
lean_dec(v_generation_5335_);
lean_dec_ref(v_proof_5334_);
lean_dec_ref(v_fact_5333_);
v_a_5361_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5363_ = v___x_5348_;
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5348_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5366_; 
if (v_isShared_5364_ == 0)
{
v___x_5366_ = v___x_5363_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
v___x_5366_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
return v___x_5366_;
}
}
}
}
else
{
lean_object* v___x_5369_; lean_object* v___x_5370_; 
lean_dec(v_generation_5335_);
lean_dec_ref(v_proof_5334_);
lean_dec_ref(v_fact_5333_);
v___x_5369_ = lean_box(0);
v___x_5370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5370_, 0, v___x_5369_);
return v___x_5370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5371_, lean_object* v_proof_5372_, lean_object* v_generation_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_, lean_object* v_a_5382_, lean_object* v_a_5383_, lean_object* v_a_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l_Lean_Meta_Grind_add(v_fact_5371_, v_proof_5372_, v_generation_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_, v_a_5381_, v_a_5382_, v_a_5383_);
lean_dec(v_a_5383_);
lean_dec_ref(v_a_5382_);
lean_dec(v_a_5381_);
lean_dec_ref(v_a_5380_);
lean_dec(v_a_5379_);
lean_dec_ref(v_a_5378_);
lean_dec(v_a_5377_);
lean_dec_ref(v_a_5376_);
lean_dec(v_a_5375_);
lean_dec(v_a_5374_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5386_, lean_object* v_generation_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_){
_start:
{
lean_object* v___x_5399_; 
lean_inc(v_fvarId_5386_);
v___x_5399_ = l_Lean_FVarId_getType___redArg(v_fvarId_5386_, v_a_5394_, v_a_5396_, v_a_5397_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_object* v_a_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
v_a_5400_ = lean_ctor_get(v___x_5399_, 0);
lean_inc(v_a_5400_);
lean_dec_ref_known(v___x_5399_, 1);
v___x_5401_ = l_Lean_mkFVar(v_fvarId_5386_);
v___x_5402_ = l_Lean_Meta_Grind_add(v_a_5400_, v___x_5401_, v_generation_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_);
return v___x_5402_;
}
else
{
lean_object* v_a_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5410_; 
lean_dec(v_generation_5387_);
lean_dec(v_fvarId_5386_);
v_a_5403_ = lean_ctor_get(v___x_5399_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5405_ = v___x_5399_;
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_a_5403_);
lean_dec(v___x_5399_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5408_; 
if (v_isShared_5406_ == 0)
{
v___x_5408_ = v___x_5405_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5411_, lean_object* v_generation_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5411_, v_generation_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec(v_a_5420_);
lean_dec_ref(v_a_5419_);
lean_dec(v_a_5418_);
lean_dec_ref(v_a_5417_);
lean_dec(v_a_5416_);
lean_dec_ref(v_a_5415_);
lean_dec(v_a_5414_);
lean_dec(v_a_5413_);
return v_res_5424_;
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
