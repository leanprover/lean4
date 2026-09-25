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
lean_object* v___x_164_; lean_object* v_env_165_; lean_object* v___x_166_; lean_object* v_toCold_167_; lean_object* v_mctx_168_; lean_object* v_lctx_169_; lean_object* v_options_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_164_ = lean_st_ref_get(v___y_162_);
v_env_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc_ref(v_env_165_);
lean_dec(v___x_164_);
v___x_166_ = lean_st_ref_get(v___y_160_);
v_toCold_167_ = lean_ctor_get(v___y_161_, 0);
v_mctx_168_ = lean_ctor_get(v___x_166_, 0);
lean_inc_ref(v_mctx_168_);
lean_dec(v___x_166_);
v_lctx_169_ = lean_ctor_get(v___y_159_, 2);
v_options_170_ = lean_ctor_get(v_toCold_167_, 2);
lean_inc_ref(v_options_170_);
lean_inc_ref(v_lctx_169_);
v___x_171_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_171_, 0, v_env_165_);
lean_ctor_set(v___x_171_, 1, v_mctx_168_);
lean_ctor_set(v___x_171_, 2, v_lctx_169_);
lean_ctor_set(v___x_171_, 3, v_options_170_);
v___x_172_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v_msgData_158_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2___boxed(lean_object* v_msgData_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msgData_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_180_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_181_; double v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_float_of_nat(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(lean_object* v_cls_186_, lean_object* v_msg_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_ref_193_; lean_object* v___x_194_; lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_239_; 
v_ref_193_ = lean_ctor_get(v___y_190_, 2);
v___x_194_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msg_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_239_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_239_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_239_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v_traceState_200_; lean_object* v_env_201_; lean_object* v_nextMacroScope_202_; lean_object* v_ngen_203_; lean_object* v_auxDeclNGen_204_; lean_object* v_cache_205_; lean_object* v_messages_206_; lean_object* v_infoState_207_; lean_object* v_snapshotTasks_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_238_; 
v___x_199_ = lean_st_ref_take(v___y_191_);
v_traceState_200_ = lean_ctor_get(v___x_199_, 4);
v_env_201_ = lean_ctor_get(v___x_199_, 0);
v_nextMacroScope_202_ = lean_ctor_get(v___x_199_, 1);
v_ngen_203_ = lean_ctor_get(v___x_199_, 2);
v_auxDeclNGen_204_ = lean_ctor_get(v___x_199_, 3);
v_cache_205_ = lean_ctor_get(v___x_199_, 5);
v_messages_206_ = lean_ctor_get(v___x_199_, 6);
v_infoState_207_ = lean_ctor_get(v___x_199_, 7);
v_snapshotTasks_208_ = lean_ctor_get(v___x_199_, 8);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_238_ == 0)
{
v___x_210_ = v___x_199_;
v_isShared_211_ = v_isSharedCheck_238_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_snapshotTasks_208_);
lean_inc(v_infoState_207_);
lean_inc(v_messages_206_);
lean_inc(v_cache_205_);
lean_inc(v_traceState_200_);
lean_inc(v_auxDeclNGen_204_);
lean_inc(v_ngen_203_);
lean_inc(v_nextMacroScope_202_);
lean_inc(v_env_201_);
lean_dec(v___x_199_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_238_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
uint64_t v_tid_212_; lean_object* v_traces_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_237_; 
v_tid_212_ = lean_ctor_get_uint64(v_traceState_200_, sizeof(void*)*1);
v_traces_213_ = lean_ctor_get(v_traceState_200_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_traceState_200_);
if (v_isSharedCheck_237_ == 0)
{
v___x_215_ = v_traceState_200_;
v_isShared_216_ = v_isSharedCheck_237_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_traces_213_);
lean_dec(v_traceState_200_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_237_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; double v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_217_ = lean_box(0);
v___x_218_ = lean_box(0);
v___x_219_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0);
v___x_220_ = 0;
v___x_221_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
v___x_222_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_222_, 0, v_cls_186_);
lean_ctor_set(v___x_222_, 1, v___x_218_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
lean_ctor_set_float(v___x_222_, sizeof(void*)*3, v___x_219_);
lean_ctor_set_float(v___x_222_, sizeof(void*)*3 + 8, v___x_219_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*3 + 16, v___x_220_);
v___x_223_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2));
v___x_224_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v_a_195_);
lean_ctor_set(v___x_224_, 2, v___x_223_);
lean_inc(v_ref_193_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v_ref_193_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = l_Lean_PersistentArray_push___redArg(v_traces_213_, v___x_225_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_226_);
v___x_228_ = v___x_215_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_226_);
lean_ctor_set_uint64(v_reuseFailAlloc_236_, sizeof(void*)*1, v_tid_212_);
v___x_228_ = v_reuseFailAlloc_236_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_230_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 4, v___x_228_);
v___x_230_ = v___x_210_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_env_201_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_nextMacroScope_202_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_ngen_203_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_auxDeclNGen_204_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_235_, 5, v_cache_205_);
lean_ctor_set(v_reuseFailAlloc_235_, 6, v_messages_206_);
lean_ctor_set(v_reuseFailAlloc_235_, 7, v_infoState_207_);
lean_ctor_set(v_reuseFailAlloc_235_, 8, v_snapshotTasks_208_);
v___x_230_ = v_reuseFailAlloc_235_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_231_ = lean_st_ref_put(v___y_191_, v___x_230_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_217_);
v___x_233_ = v___x_197_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_217_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* v___x_275_, lean_object* v_x_276_, size_t v_x_277_, lean_object* v_x_278_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_object* v_es_279_; lean_object* v___x_280_; size_t v___x_281_; size_t v___x_282_; lean_object* v_j_283_; lean_object* v_entry_284_; 
v_es_279_ = lean_ctor_get(v_x_276_, 0);
v___x_280_ = lean_box(2);
v___x_281_ = ((size_t)31ULL);
v___x_282_ = lean_usize_land(v_x_277_, v___x_281_);
v_j_283_ = lean_usize_to_nat(v___x_282_);
v_entry_284_ = lean_array_get(v___x_280_, v_es_279_, v_j_283_);
switch(lean_obj_tag(v_entry_284_))
{
case 0:
{
lean_object* v_key_285_; uint8_t v___x_286_; 
v_key_285_ = lean_ctor_get(v_entry_284_, 0);
lean_inc(v_key_285_);
lean_dec_ref_known(v_entry_284_, 2);
v___x_286_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_275_, v_x_278_, v_key_285_);
if (v___x_286_ == 0)
{
lean_dec(v_j_283_);
return v_x_276_;
}
else
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
lean_inc_ref(v_es_279_);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_x_276_, 0);
lean_dec(v_unused_295_);
v___x_288_ = v_x_276_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_dec(v_x_276_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_array_set(v_es_279_, v_j_283_, v___x_280_);
lean_dec(v_j_283_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
case 1:
{
lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_330_; 
lean_inc_ref(v_es_279_);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v_x_276_, 0);
lean_dec(v_unused_331_);
v___x_297_ = v_x_276_;
v_isShared_298_ = v_isSharedCheck_330_;
goto v_resetjp_296_;
}
else
{
lean_dec(v_x_276_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_330_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v_node_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_329_; 
v_node_299_ = lean_ctor_get(v_entry_284_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_entry_284_);
if (v_isSharedCheck_329_ == 0)
{
v___x_301_ = v_entry_284_;
v_isShared_302_ = v_isSharedCheck_329_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_node_299_);
lean_dec(v_entry_284_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_329_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
size_t v___x_303_; lean_object* v_entries_304_; size_t v___x_305_; lean_object* v_newNode_306_; lean_object* v___x_307_; 
v___x_303_ = ((size_t)5ULL);
v_entries_304_ = lean_array_set(v_es_279_, v_j_283_, v___x_280_);
v___x_305_ = lean_usize_shift_right(v_x_277_, v___x_303_);
v_newNode_306_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_275_, v_node_299_, v___x_305_, v_x_278_);
lean_inc_ref(v_newNode_306_);
v___x_307_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_306_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_309_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v_newNode_306_);
v___x_309_ = v___x_301_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_newNode_306_);
v___x_309_ = v_reuseFailAlloc_314_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_array_set(v_entries_304_, v_j_283_, v___x_309_);
lean_dec(v_j_283_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_310_);
v___x_312_ = v___x_297_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v_val_315_; lean_object* v_fst_316_; lean_object* v_snd_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_328_; 
lean_dec_ref(v_newNode_306_);
lean_del_object(v___x_301_);
v_val_315_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_val_315_);
lean_dec_ref_known(v___x_307_, 1);
v_fst_316_ = lean_ctor_get(v_val_315_, 0);
v_snd_317_ = lean_ctor_get(v_val_315_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_val_315_);
if (v_isSharedCheck_328_ == 0)
{
v___x_319_ = v_val_315_;
v_isShared_320_ = v_isSharedCheck_328_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_snd_317_);
lean_inc(v_fst_316_);
lean_dec(v_val_315_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_328_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_fst_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_snd_317_);
v___x_322_ = v_reuseFailAlloc_327_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_array_set(v_entries_304_, v_j_283_, v___x_322_);
lean_dec(v_j_283_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_323_);
v___x_325_ = v___x_297_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_283_);
lean_dec_ref(v_x_278_);
return v_x_276_;
}
}
}
else
{
lean_object* v_ks_332_; lean_object* v_vs_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_347_; 
v_ks_332_ = lean_ctor_get(v_x_276_, 0);
v_vs_333_ = lean_ctor_get(v_x_276_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_347_ == 0)
{
v___x_335_ = v_x_276_;
v_isShared_336_ = v_isSharedCheck_347_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_vs_333_);
lean_inc(v_ks_332_);
lean_dec(v_x_276_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_347_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; 
v___x_337_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_275_, v_ks_332_, v_x_278_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v___x_339_; 
if (v_isShared_336_ == 0)
{
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_ks_332_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_vs_333_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
else
{
lean_object* v_val_341_; lean_object* v_keys_x27_342_; lean_object* v_vals_x27_343_; lean_object* v___x_345_; 
v_val_341_ = lean_ctor_get(v___x_337_, 0);
lean_inc_n(v_val_341_, 2);
lean_dec_ref_known(v___x_337_, 1);
v_keys_x27_342_ = l_Array_eraseIdx___redArg(v_ks_332_, v_val_341_);
v_vals_x27_343_ = l_Array_eraseIdx___redArg(v_vs_333_, v_val_341_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_vals_x27_343_);
lean_ctor_set(v___x_335_, 0, v_keys_x27_342_);
v___x_345_ = v___x_335_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_keys_x27_342_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_vals_x27_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* v___x_348_, lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
size_t v_x_22521__boxed_352_; lean_object* v_res_353_; 
v_x_22521__boxed_352_ = lean_unbox_usize(v_x_350_);
lean_dec(v_x_350_);
v_res_353_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_348_, v_x_349_, v_x_22521__boxed_352_, v_x_351_);
lean_dec_ref(v___x_348_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_354_, lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
uint64_t v___x_357_; size_t v_h_358_; lean_object* v___x_359_; 
lean_inc_ref(v_x_356_);
v___x_357_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_354_, v_x_356_);
v_h_358_ = lean_uint64_to_usize(v___x_357_);
v___x_359_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_354_, v_x_355_, v_h_358_, v_x_356_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg___boxed(lean_object* v___x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_360_, v_x_361_, v_x_362_);
lean_dec_ref(v___x_360_);
return v_res_363_;
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
lean_object* v_head_394_; lean_object* v_tail_395_; lean_object* v___x_396_; lean_object* v___y_398_; uint8_t v_a_438_; uint8_t v___x_452_; 
v_head_394_ = lean_ctor_get(v_as_x27_380_, 0);
v_tail_395_ = lean_ctor_get(v_as_x27_380_, 1);
v___x_396_ = lean_box(0);
v___x_452_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_394_);
if (v___x_452_ == 0)
{
v_a_438_ = v___x_452_;
goto v___jp_437_;
}
else
{
lean_object* v___x_453_; 
lean_inc(v_head_394_);
v___x_453_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_394_, v___y_382_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; uint8_t v___x_455_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
v___x_455_ = lean_unbox(v_a_454_);
lean_dec(v_a_454_);
v_a_438_ = v___x_455_;
goto v___jp_437_;
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_453_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_453_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
v___jp_397_:
{
lean_object* v___x_399_; lean_object* v_toGoalState_400_; lean_object* v_mvarId_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_436_; 
v___x_399_ = lean_st_ref_take(v___y_398_);
v_toGoalState_400_ = lean_ctor_get(v___x_399_, 0);
v_mvarId_401_ = lean_ctor_get(v___x_399_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_436_ == 0)
{
v___x_403_ = v___x_399_;
v_isShared_404_ = v_isSharedCheck_436_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_mvarId_401_);
lean_inc(v_toGoalState_400_);
lean_dec(v___x_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_436_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_nextDeclIdx_405_; lean_object* v_enodeMap_406_; lean_object* v_exprs_407_; lean_object* v_parents_408_; lean_object* v_congrTable_409_; lean_object* v_appMap_410_; lean_object* v_indicesFound_411_; lean_object* v_newFacts_412_; uint8_t v_inconsistent_413_; lean_object* v_nextIdx_414_; lean_object* v_newRawFacts_415_; lean_object* v_facts_416_; lean_object* v_extThms_417_; lean_object* v_ematch_418_; lean_object* v_inj_419_; lean_object* v_split_420_; lean_object* v_clean_421_; lean_object* v_sstates_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_435_; 
v_nextDeclIdx_405_ = lean_ctor_get(v_toGoalState_400_, 0);
v_enodeMap_406_ = lean_ctor_get(v_toGoalState_400_, 1);
v_exprs_407_ = lean_ctor_get(v_toGoalState_400_, 2);
v_parents_408_ = lean_ctor_get(v_toGoalState_400_, 3);
v_congrTable_409_ = lean_ctor_get(v_toGoalState_400_, 4);
v_appMap_410_ = lean_ctor_get(v_toGoalState_400_, 5);
v_indicesFound_411_ = lean_ctor_get(v_toGoalState_400_, 6);
v_newFacts_412_ = lean_ctor_get(v_toGoalState_400_, 7);
v_inconsistent_413_ = lean_ctor_get_uint8(v_toGoalState_400_, sizeof(void*)*17);
v_nextIdx_414_ = lean_ctor_get(v_toGoalState_400_, 8);
v_newRawFacts_415_ = lean_ctor_get(v_toGoalState_400_, 9);
v_facts_416_ = lean_ctor_get(v_toGoalState_400_, 10);
v_extThms_417_ = lean_ctor_get(v_toGoalState_400_, 11);
v_ematch_418_ = lean_ctor_get(v_toGoalState_400_, 12);
v_inj_419_ = lean_ctor_get(v_toGoalState_400_, 13);
v_split_420_ = lean_ctor_get(v_toGoalState_400_, 14);
v_clean_421_ = lean_ctor_get(v_toGoalState_400_, 15);
v_sstates_422_ = lean_ctor_get(v_toGoalState_400_, 16);
v_isSharedCheck_435_ = !lean_is_exclusive(v_toGoalState_400_);
if (v_isSharedCheck_435_ == 0)
{
v___x_424_ = v_toGoalState_400_;
v_isShared_425_ = v_isSharedCheck_435_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_sstates_422_);
lean_inc(v_clean_421_);
lean_inc(v_split_420_);
lean_inc(v_inj_419_);
lean_inc(v_ematch_418_);
lean_inc(v_extThms_417_);
lean_inc(v_facts_416_);
lean_inc(v_newRawFacts_415_);
lean_inc(v_nextIdx_414_);
lean_inc(v_newFacts_412_);
lean_inc(v_indicesFound_411_);
lean_inc(v_appMap_410_);
lean_inc(v_congrTable_409_);
lean_inc(v_parents_408_);
lean_inc(v_exprs_407_);
lean_inc(v_enodeMap_406_);
lean_inc(v_nextDeclIdx_405_);
lean_dec(v_toGoalState_400_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_435_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
lean_inc(v_head_394_);
v___x_426_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_406_, v_congrTable_409_, v_head_394_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 4, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_nextDeclIdx_405_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_enodeMap_406_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_exprs_407_);
lean_ctor_set(v_reuseFailAlloc_434_, 3, v_parents_408_);
lean_ctor_set(v_reuseFailAlloc_434_, 4, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_434_, 5, v_appMap_410_);
lean_ctor_set(v_reuseFailAlloc_434_, 6, v_indicesFound_411_);
lean_ctor_set(v_reuseFailAlloc_434_, 7, v_newFacts_412_);
lean_ctor_set(v_reuseFailAlloc_434_, 8, v_nextIdx_414_);
lean_ctor_set(v_reuseFailAlloc_434_, 9, v_newRawFacts_415_);
lean_ctor_set(v_reuseFailAlloc_434_, 10, v_facts_416_);
lean_ctor_set(v_reuseFailAlloc_434_, 11, v_extThms_417_);
lean_ctor_set(v_reuseFailAlloc_434_, 12, v_ematch_418_);
lean_ctor_set(v_reuseFailAlloc_434_, 13, v_inj_419_);
lean_ctor_set(v_reuseFailAlloc_434_, 14, v_split_420_);
lean_ctor_set(v_reuseFailAlloc_434_, 15, v_clean_421_);
lean_ctor_set(v_reuseFailAlloc_434_, 16, v_sstates_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_434_, sizeof(void*)*17, v_inconsistent_413_);
v___x_428_ = v_reuseFailAlloc_434_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_428_);
v___x_430_ = v___x_403_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_mvarId_401_);
v___x_430_ = v_reuseFailAlloc_433_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; 
v___x_431_ = lean_st_ref_put(v___y_398_, v___x_430_);
v_as_x27_380_ = v_tail_395_;
v_b_381_ = v___x_396_;
goto _start;
}
}
}
}
}
v___jp_437_:
{
if (v_a_438_ == 0)
{
v_as_x27_380_ = v_tail_395_;
v_b_381_ = v___x_396_;
goto _start;
}
else
{
lean_object* v_toCold_440_; lean_object* v_options_441_; uint8_t v_hasTrace_442_; 
v_toCold_440_ = lean_ctor_get(v___y_390_, 0);
v_options_441_ = lean_ctor_get(v_toCold_440_, 2);
v_hasTrace_442_ = lean_ctor_get_uint8(v_options_441_, sizeof(void*)*1);
if (v_hasTrace_442_ == 0)
{
v___y_398_ = v___y_382_;
goto v___jp_397_;
}
else
{
lean_object* v_inheritedTraceOptions_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_inheritedTraceOptions_443_ = lean_ctor_get(v_toCold_440_, 11);
v___x_444_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_445_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_446_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_443_, v_options_441_, v___x_445_);
if (v___x_446_ == 0)
{
v___y_398_ = v___y_382_;
goto v___jp_397_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_Grind_updateLastTag(v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec_ref_known(v___x_447_, 1);
v___x_448_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_394_);
v___x_449_ = l_Lean_MessageData_ofExpr(v_head_394_);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_444_, v___x_450_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_dec_ref_known(v___x_451_, 1);
v___y_398_ = v___y_382_;
goto v___jp_397_;
}
else
{
return v___x_451_;
}
}
else
{
return v___x_447_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_464_, lean_object* v_b_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_464_, v_b_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec(v___y_466_);
lean_dec(v_as_x27_464_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_Grind_getParents___redArg(v_root_478_, v_a_479_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_491_);
v___x_493_ = lean_box(0);
v___x_494_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_492_, v___x_493_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec(v___x_492_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v___x_494_, 0);
lean_dec(v_unused_502_);
v___x_496_ = v___x_494_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_dec(v___x_494_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v_a_491_);
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_491_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec(v_a_491_);
v_a_503_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_494_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_494_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
else
{
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_a_520_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_root_511_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_524_, lean_object* v_00_u03b2_525_, lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_524_, v_x_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_529_, lean_object* v_00_u03b2_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_529_, v_00_u03b2_530_, v_x_531_, v_x_532_);
lean_dec_ref(v___x_529_);
return v_res_533_;
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
lean_dec(v_as_x27_579_);
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
size_t v_x_22983__boxed_605_; lean_object* v_res_606_; 
v_x_22983__boxed_605_ = lean_unbox_usize(v_x_603_);
lean_dec(v_x_603_);
v_res_606_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_600_, v_00_u03b2_601_, v_x_602_, v_x_22983__boxed_605_, v_x_604_);
lean_dec_ref(v___x_600_);
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
lean_object* v_head_624_; lean_object* v_tail_625_; lean_object* v___x_626_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; uint8_t v_a_641_; uint8_t v___x_655_; 
v_head_624_ = lean_ctor_get(v_as_x27_610_, 0);
v_tail_625_ = lean_ctor_get(v_as_x27_610_, 1);
v___x_626_ = lean_box(0);
v___x_655_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_624_);
if (v___x_655_ == 0)
{
v_a_641_ = v___x_655_;
goto v___jp_640_;
}
else
{
lean_object* v___x_656_; 
lean_inc(v_head_624_);
v___x_656_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_624_, v___y_612_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; uint8_t v___x_658_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = lean_unbox(v_a_657_);
lean_dec(v_a_657_);
v_a_641_ = v___x_658_;
goto v___jp_640_;
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_a_659_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_656_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_656_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
v___jp_627_:
{
lean_object* v___x_638_; 
lean_inc(v_head_624_);
v___x_638_ = l_Lean_Meta_Grind_addCongrTable(v_head_624_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_dec_ref_known(v___x_638_, 1);
v_as_x27_610_ = v_tail_625_;
v_b_611_ = v___x_626_;
goto _start;
}
else
{
return v___x_638_;
}
}
v___jp_640_:
{
if (v_a_641_ == 0)
{
v_as_x27_610_ = v_tail_625_;
v_b_611_ = v___x_626_;
goto _start;
}
else
{
lean_object* v_toCold_643_; lean_object* v_options_644_; uint8_t v_hasTrace_645_; 
v_toCold_643_ = lean_ctor_get(v___y_620_, 0);
v_options_644_ = lean_ctor_get(v_toCold_643_, 2);
v_hasTrace_645_ = lean_ctor_get_uint8(v_options_644_, sizeof(void*)*1);
if (v_hasTrace_645_ == 0)
{
v___y_628_ = v___y_612_;
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
goto v___jp_627_;
}
else
{
lean_object* v_inheritedTraceOptions_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_inheritedTraceOptions_646_ = lean_ctor_get(v_toCold_643_, 11);
v___x_647_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_648_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_649_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_646_, v_options_644_, v___x_648_);
if (v___x_649_ == 0)
{
v___y_628_ = v___y_612_;
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
goto v___jp_627_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Meta_Grind_updateLastTag(v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec_ref_known(v___x_650_, 1);
v___x_651_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_624_);
v___x_652_ = l_Lean_MessageData_ofExpr(v_head_624_);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_647_, v___x_653_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_dec_ref_known(v___x_654_, 1);
v___y_628_ = v___y_612_;
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
goto v___jp_627_;
}
else
{
return v___x_654_;
}
}
else
{
return v___x_650_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_667_, lean_object* v_b_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_667_, v_b_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec(v___y_669_);
lean_dec(v_as_x27_667_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_681_);
v___x_694_ = lean_box(0);
v___x_695_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_693_, v___x_694_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
lean_dec(v___x_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v___x_695_, 0);
lean_dec(v_unused_703_);
v___x_697_ = v___x_695_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_dec(v___x_695_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_694_);
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_694_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
else
{
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec(v_a_705_);
lean_dec(v_parents_704_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_717_, lean_object* v_as_x27_718_, lean_object* v_b_719_, lean_object* v_a_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_718_, v_b_719_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_733_, lean_object* v_as_x27_734_, lean_object* v_b_735_, lean_object* v_a_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_733_, v_as_x27_734_, v_b_735_, v_a_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v___y_737_);
lean_dec(v_as_x27_734_);
lean_dec(v_as_733_);
return v_res_748_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_749_, lean_object* v_i_750_, lean_object* v_k_751_){
_start:
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = lean_array_get_size(v_keys_749_);
v___x_753_ = lean_nat_dec_lt(v_i_750_, v___x_752_);
if (v___x_753_ == 0)
{
lean_dec(v_i_750_);
return v___x_753_;
}
else
{
lean_object* v_k_x27_754_; uint8_t v___x_755_; 
v_k_x27_754_ = lean_array_fget_borrowed(v_keys_749_, v_i_750_);
v___x_755_ = l_Lean_instBEqMVarId_beq(v_k_751_, v_k_x27_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_add(v_i_750_, v___x_756_);
lean_dec(v_i_750_);
v_i_750_ = v___x_757_;
goto _start;
}
else
{
lean_dec(v_i_750_);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_759_, lean_object* v_i_760_, lean_object* v_k_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_759_, v_i_760_, v_k_761_);
lean_dec(v_k_761_);
lean_dec_ref(v_keys_759_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_764_, size_t v_x_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_764_) == 0)
{
lean_object* v_es_767_; lean_object* v___x_768_; size_t v___x_769_; size_t v___x_770_; lean_object* v_j_771_; lean_object* v___x_772_; 
v_es_767_ = lean_ctor_get(v_x_764_, 0);
v___x_768_ = lean_box(2);
v___x_769_ = ((size_t)31ULL);
v___x_770_ = lean_usize_land(v_x_765_, v___x_769_);
v_j_771_ = lean_usize_to_nat(v___x_770_);
v___x_772_ = lean_array_get_borrowed(v___x_768_, v_es_767_, v_j_771_);
lean_dec(v_j_771_);
switch(lean_obj_tag(v___x_772_))
{
case 0:
{
lean_object* v_key_773_; uint8_t v___x_774_; 
v_key_773_ = lean_ctor_get(v___x_772_, 0);
v___x_774_ = l_Lean_instBEqMVarId_beq(v_x_766_, v_key_773_);
return v___x_774_;
}
case 1:
{
lean_object* v_node_775_; size_t v___x_776_; size_t v___x_777_; 
v_node_775_ = lean_ctor_get(v___x_772_, 0);
v___x_776_ = ((size_t)5ULL);
v___x_777_ = lean_usize_shift_right(v_x_765_, v___x_776_);
v_x_764_ = v_node_775_;
v_x_765_ = v___x_777_;
goto _start;
}
default: 
{
uint8_t v___x_779_; 
v___x_779_ = 0;
return v___x_779_;
}
}
}
else
{
lean_object* v_ks_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_ks_780_ = lean_ctor_get(v_x_764_, 0);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_780_, v___x_781_, v_x_766_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_783_, lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
size_t v_x_9681__boxed_786_; uint8_t v_res_787_; lean_object* v_r_788_; 
v_x_9681__boxed_786_ = lean_unbox_usize(v_x_784_);
lean_dec(v_x_784_);
v_res_787_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_783_, v_x_9681__boxed_786_, v_x_785_);
lean_dec(v_x_785_);
lean_dec_ref(v_x_783_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
uint64_t v___x_791_; size_t v___x_792_; uint8_t v___x_793_; 
v___x_791_ = l_Lean_instHashableMVarId_hash(v_x_790_);
v___x_792_ = lean_uint64_to_usize(v___x_791_);
v___x_793_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_789_, v___x_792_, v_x_790_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_794_, lean_object* v_x_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_794_, v_x_795_);
lean_dec(v_x_795_);
lean_dec_ref(v_x_794_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v_mctx_802_; lean_object* v_eAssignment_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_801_ = lean_st_ref_get(v___y_799_);
v_mctx_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc_ref(v_mctx_802_);
lean_dec(v___x_801_);
v_eAssignment_803_ = lean_ctor_get(v_mctx_802_, 8);
lean_inc_ref(v_eAssignment_803_);
lean_dec_ref(v_mctx_802_);
v___x_804_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_803_, v_mvarId_798_);
lean_dec_ref(v_eAssignment_803_);
v___x_805_ = lean_box(v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec(v_mvarId_807_);
return v_res_810_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_821_ = l_Lean_mkConst(v___x_820_, v___x_819_);
return v___x_821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_box(0);
v___x_828_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_829_ = l_Lean_mkConst(v___x_828_, v___x_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v___x_841_; lean_object* v_mvarId_842_; lean_object* v___x_843_; lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_897_; 
v___x_841_ = lean_st_ref_get(v_a_830_);
v_mvarId_842_ = lean_ctor_get(v___x_841_, 1);
lean_inc(v_mvarId_842_);
lean_dec(v___x_841_);
v___x_843_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_842_, v_a_837_);
lean_dec(v_mvarId_842_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_897_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_897_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_897_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
uint8_t v___x_848_; 
v___x_848_ = lean_unbox(v_a_844_);
lean_dec(v_a_844_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
lean_del_object(v___x_846_);
v___x_849_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_834_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
v___x_851_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_850_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
v___x_853_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_834_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_834_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_859_ = l_Lean_mkApp4(v___x_857_, v_a_854_, v_a_856_, v_a_852_, v___x_858_);
v___x_860_ = l_Lean_Meta_Grind_closeGoal(v___x_859_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
return v___x_860_;
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_a_854_);
lean_dec(v_a_852_);
v_a_861_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_855_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_855_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec(v_a_852_);
v_a_869_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_853_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_853_);
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
v_a_877_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_851_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_851_);
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
v_a_885_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_849_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_849_);
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
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = lean_box(0);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_893_);
v___x_895_ = v___x_846_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec(v_a_898_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_910_, v___y_918_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec(v___y_924_);
lean_dec(v_mvarId_923_);
return v_res_935_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_936_, lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
uint8_t v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_937_, v_x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
uint8_t v_res_943_; lean_object* v_r_944_; 
v_res_943_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_940_, v_x_941_, v_x_942_);
lean_dec(v_x_942_);
lean_dec_ref(v_x_941_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_945_, lean_object* v_x_946_, size_t v_x_947_, lean_object* v_x_948_){
_start:
{
uint8_t v___x_949_; 
v___x_949_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_946_, v_x_947_, v_x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
size_t v_x_9964__boxed_954_; uint8_t v_res_955_; lean_object* v_r_956_; 
v_x_9964__boxed_954_ = lean_unbox_usize(v_x_952_);
lean_dec(v_x_952_);
v_res_955_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_950_, v_x_951_, v_x_9964__boxed_954_, v_x_953_);
lean_dec(v_x_953_);
lean_dec_ref(v_x_951_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_957_, lean_object* v_keys_958_, lean_object* v_vals_959_, lean_object* v_heq_960_, lean_object* v_i_961_, lean_object* v_k_962_){
_start:
{
uint8_t v___x_963_; 
v___x_963_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_958_, v_i_961_, v_k_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_964_, lean_object* v_keys_965_, lean_object* v_vals_966_, lean_object* v_heq_967_, lean_object* v_i_968_, lean_object* v_k_969_){
_start:
{
uint8_t v_res_970_; lean_object* v_r_971_; 
v_res_970_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_964_, v_keys_965_, v_vals_966_, v_heq_967_, v_i_968_, v_k_969_);
lean_dec(v_k_969_);
lean_dec_ref(v_vals_966_);
lean_dec_ref(v_keys_965_);
v_r_971_ = lean_box(v_res_970_);
return v_r_971_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_box(0);
v___x_976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_977_ = l_Lean_mkConst(v___x_976_, v___x_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_978_, lean_object* v_rhs_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; 
lean_inc_ref(v_rhs_979_);
lean_inc_ref(v_lhs_978_);
v___x_991_ = l_Lean_Meta_mkEq(v_lhs_978_, v_rhs_979_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
lean_inc(v_a_989_);
lean_inc_ref(v_a_988_);
lean_inc(v_a_987_);
lean_inc_ref(v_a_986_);
lean_inc(v_a_985_);
lean_inc_ref(v_a_984_);
lean_inc(v_a_983_);
lean_inc_ref(v_a_982_);
lean_inc(v_a_981_);
lean_inc(v_a_980_);
v___x_993_ = lean_grind_mk_eq_proof(v_lhs_978_, v_rhs_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
lean_inc(v_a_992_);
v___x_995_ = l_Lean_Meta_mkDecide(v_a_992_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v___x_997_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_998_ = l_Lean_Expr_appArg_x21(v_a_996_);
lean_dec(v_a_996_);
v___x_999_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_992_);
v___x_1000_ = l_Lean_mkApp3(v___x_997_, v_a_992_, v___x_998_, v___x_999_);
v___x_1001_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_984_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1004_ = l_Lean_mkApp4(v___x_1003_, v_a_992_, v_a_1002_, v___x_1000_, v_a_994_);
v___x_1005_ = l_Lean_Meta_Grind_closeGoal(v___x_1004_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
return v___x_1005_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v___x_1000_);
lean_dec(v_a_994_);
lean_dec(v_a_992_);
v_a_1006_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1001_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1001_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_a_994_);
lean_dec(v_a_992_);
v_a_1014_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_995_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_995_);
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
lean_dec(v_a_992_);
v_a_1022_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_993_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_993_);
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
lean_dec_ref(v_rhs_979_);
lean_dec_ref(v_lhs_978_);
v_a_1030_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_991_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_991_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1038_, lean_object* v_rhs_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1038_, v_rhs_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec(v_a_1040_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1052_, lean_object* v_as_x27_1053_, lean_object* v_b_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
if (lean_obj_tag(v_as_x27_1053_) == 0)
{
lean_object* v___x_1066_; 
lean_dec(v___x_1052_);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v_b_1054_);
return v___x_1066_;
}
else
{
lean_object* v_head_1067_; lean_object* v_tail_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_head_1067_ = lean_ctor_get(v_as_x27_1053_, 0);
v_tail_1068_ = lean_ctor_get(v_as_x27_1053_, 1);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_st_ref_get(v___y_1055_);
lean_inc(v_head_1067_);
v___x_1071_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1070_, v_head_1067_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___x_1070_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v_self_1073_; lean_object* v_next_1074_; lean_object* v_root_1075_; lean_object* v_congr_1076_; lean_object* v_target_x3f_1077_; lean_object* v_proof_x3f_1078_; uint8_t v_flipped_1079_; lean_object* v_size_1080_; uint8_t v_interpreted_1081_; uint8_t v_ctor_1082_; uint8_t v_hasLambdas_1083_; uint8_t v_heqProofs_1084_; lean_object* v_idx_1085_; lean_object* v_generation_1086_; lean_object* v_mt_1087_; lean_object* v_sTerms_1088_; uint8_t v_funCC_1089_; lean_object* v_ematchDiagSource_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1102_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v_self_1073_ = lean_ctor_get(v_a_1072_, 0);
v_next_1074_ = lean_ctor_get(v_a_1072_, 1);
v_root_1075_ = lean_ctor_get(v_a_1072_, 2);
v_congr_1076_ = lean_ctor_get(v_a_1072_, 3);
v_target_x3f_1077_ = lean_ctor_get(v_a_1072_, 4);
v_proof_x3f_1078_ = lean_ctor_get(v_a_1072_, 5);
v_flipped_1079_ = lean_ctor_get_uint8(v_a_1072_, sizeof(void*)*12);
v_size_1080_ = lean_ctor_get(v_a_1072_, 6);
v_interpreted_1081_ = lean_ctor_get_uint8(v_a_1072_, sizeof(void*)*12 + 1);
v_ctor_1082_ = lean_ctor_get_uint8(v_a_1072_, sizeof(void*)*12 + 2);
v_hasLambdas_1083_ = lean_ctor_get_uint8(v_a_1072_, sizeof(void*)*12 + 3);
v_heqProofs_1084_ = lean_ctor_get_uint8(v_a_1072_, sizeof(void*)*12 + 4);
v_idx_1085_ = lean_ctor_get(v_a_1072_, 7);
v_generation_1086_ = lean_ctor_get(v_a_1072_, 8);
v_mt_1087_ = lean_ctor_get(v_a_1072_, 9);
v_sTerms_1088_ = lean_ctor_get(v_a_1072_, 10);
v_funCC_1089_ = lean_ctor_get_uint8(v_a_1072_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1090_ = lean_ctor_get(v_a_1072_, 11);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_a_1072_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1092_ = v_a_1072_;
v_isShared_1093_ = v_isSharedCheck_1102_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_ematchDiagSource_1090_);
lean_inc(v_sTerms_1088_);
lean_inc(v_mt_1087_);
lean_inc(v_generation_1086_);
lean_inc(v_idx_1085_);
lean_inc(v_size_1080_);
lean_inc(v_proof_x3f_1078_);
lean_inc(v_target_x3f_1077_);
lean_inc(v_congr_1076_);
lean_inc(v_root_1075_);
lean_inc(v_next_1074_);
lean_inc(v_self_1073_);
lean_dec(v_a_1072_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1102_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
uint8_t v___x_1094_; 
v___x_1094_ = lean_nat_dec_lt(v_mt_1087_, v___x_1052_);
lean_dec(v_mt_1087_);
if (v___x_1094_ == 0)
{
lean_del_object(v___x_1092_);
lean_dec(v_ematchDiagSource_1090_);
lean_dec(v_sTerms_1088_);
lean_dec(v_generation_1086_);
lean_dec(v_idx_1085_);
lean_dec(v_size_1080_);
lean_dec(v_proof_x3f_1078_);
lean_dec(v_target_x3f_1077_);
lean_dec_ref(v_congr_1076_);
lean_dec_ref(v_root_1075_);
lean_dec_ref(v_next_1074_);
lean_dec_ref(v_self_1073_);
v_as_x27_1053_ = v_tail_1068_;
v_b_1054_ = v___x_1069_;
goto _start;
}
else
{
lean_object* v___x_1097_; 
lean_inc(v___x_1052_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 9, v___x_1052_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_self_1073_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_next_1074_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_root_1075_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v_congr_1076_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v_target_x3f_1077_);
lean_ctor_set(v_reuseFailAlloc_1101_, 5, v_proof_x3f_1078_);
lean_ctor_set(v_reuseFailAlloc_1101_, 6, v_size_1080_);
lean_ctor_set(v_reuseFailAlloc_1101_, 7, v_idx_1085_);
lean_ctor_set(v_reuseFailAlloc_1101_, 8, v_generation_1086_);
lean_ctor_set(v_reuseFailAlloc_1101_, 9, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1101_, 10, v_sTerms_1088_);
lean_ctor_set(v_reuseFailAlloc_1101_, 11, v_ematchDiagSource_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12, v_flipped_1079_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12 + 1, v_interpreted_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12 + 2, v_ctor_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12 + 3, v_hasLambdas_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12 + 4, v_heqProofs_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*12 + 5, v_funCC_1089_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; 
lean_inc(v_head_1067_);
v___x_1098_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1067_, v___x_1097_, v___y_1055_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; 
lean_dec_ref_known(v___x_1098_, 1);
v___x_1099_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1067_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_dec_ref_known(v___x_1099_, 1);
v_as_x27_1053_ = v_tail_1068_;
v_b_1054_ = v___x_1069_;
goto _start;
}
else
{
lean_dec(v___x_1052_);
return v___x_1099_;
}
}
else
{
lean_dec(v___x_1052_);
return v___x_1098_;
}
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v___x_1052_);
v_a_1103_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1071_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1071_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1123_; lean_object* v_toGoalState_1124_; lean_object* v_ematch_1125_; lean_object* v_gmt_1126_; lean_object* v___x_1127_; 
v___x_1123_ = lean_st_ref_get(v_a_1112_);
v_toGoalState_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc_ref(v_toGoalState_1124_);
lean_dec(v___x_1123_);
v_ematch_1125_ = lean_ctor_get(v_toGoalState_1124_, 12);
lean_inc_ref(v_ematch_1125_);
lean_dec_ref(v_toGoalState_1124_);
v_gmt_1126_ = lean_ctor_get(v_ematch_1125_, 1);
lean_inc(v_gmt_1126_);
lean_dec_ref(v_ematch_1125_);
v___x_1127_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1111_, v_a_1112_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1128_);
lean_dec(v_a_1128_);
v___x_1130_ = lean_box(0);
v___x_1131_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1126_, v___x_1129_, v___x_1130_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
lean_dec(v___x_1129_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v___x_1131_, 0);
lean_dec(v_unused_1139_);
v___x_1133_ = v___x_1131_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_dec(v___x_1131_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1130_);
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1130_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
return v___x_1131_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_gmt_1126_);
v_a_1140_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1127_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1127_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_root_1148_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1161_, lean_object* v_as_x27_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1161_, v_as_x27_1162_, v_b_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec(v_as_x27_1162_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1176_, lean_object* v_as_1177_, lean_object* v_as_x27_1178_, lean_object* v_b_1179_, lean_object* v_a_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1176_, v_as_x27_1178_, v_b_1179_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1193_, lean_object* v_as_1194_, lean_object* v_as_x27_1195_, lean_object* v_b_1196_, lean_object* v_a_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1193_, v_as_1194_, v_as_x27_1195_, v_b_1196_, v_a_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec(v_as_x27_1195_);
lean_dec(v_as_1194_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
if (lean_obj_tag(v_a_1210_) == 0)
{
lean_object* v___x_1212_; 
v___x_1212_ = l_List_reverse___redArg(v_a_1211_);
return v___x_1212_;
}
else
{
lean_object* v_head_1213_; lean_object* v_tail_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1223_; 
v_head_1213_ = lean_ctor_get(v_a_1210_, 0);
v_tail_1214_ = lean_ctor_get(v_a_1210_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1216_ = v_a_1210_;
v_isShared_1217_ = v_isSharedCheck_1223_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_tail_1214_);
lean_inc(v_head_1213_);
lean_dec(v_a_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1223_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = l_Lean_MessageData_ofExpr(v_head_1213_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v_a_1211_);
lean_ctor_set(v___x_1216_, 0, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_a_1211_);
v___x_1220_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
v_a_1210_ = v_tail_1214_;
v_a_1211_ = v___x_1220_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1224_, lean_object* v_a_1225_, lean_object* v_fst_1226_, lean_object* v_a_1227_, lean_object* v_lams_1228_, lean_object* v_____r_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1224_, v_a_1227_, v___y_1230_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; uint8_t v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_unbox(v_a_1279_);
lean_dec(v_a_1279_);
if (v___x_1280_ == 0)
{
goto v___jp_1241_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_inc(v_fst_1226_);
v___x_1281_ = l_Array_reverse___redArg(v_fst_1226_);
lean_inc(v_snd_1224_);
v___x_1282_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1228_, v_snd_1224_, v___x_1281_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_dec_ref_known(v___x_1282_, 1);
goto v___jp_1241_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_fst_1226_);
lean_dec(v_snd_1224_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_fst_1226_);
lean_dec(v_snd_1224_);
v_a_1291_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1278_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1278_);
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
v___jp_1241_:
{
if (lean_obj_tag(v_snd_1224_) == 5)
{
lean_object* v_fn_1242_; lean_object* v_arg_1243_; lean_object* v___x_1244_; 
v_fn_1242_ = lean_ctor_get(v_snd_1224_, 0);
lean_inc_ref(v_fn_1242_);
v_arg_1243_ = lean_ctor_get(v_snd_1224_, 1);
lean_inc_ref(v_arg_1243_);
v___x_1244_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1225_, v___y_1230_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = lean_box(0);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1231_);
lean_inc(v___y_1230_);
v___x_1247_ = lean_grind_internalize(v_snd_1224_, v_a_1245_, v___x_1246_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1257_; 
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v___x_1247_, 0);
lean_dec(v_unused_1258_);
v___x_1249_ = v___x_1247_;
v_isShared_1250_ = v_isSharedCheck_1257_;
goto v_resetjp_1248_;
}
else
{
lean_dec(v___x_1247_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1257_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1251_ = lean_array_push(v_fst_1226_, v_arg_1243_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v_fn_1242_);
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1253_);
v___x_1255_ = v___x_1249_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v_arg_1243_);
lean_dec_ref(v_fn_1242_);
lean_dec(v_fst_1226_);
v_a_1259_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1247_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1247_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref(v_arg_1243_);
lean_dec_ref_known(v_snd_1224_, 2);
lean_dec_ref(v_fn_1242_);
lean_dec(v_fst_1226_);
v_a_1267_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1244_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1244_);
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
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v_fst_1226_);
lean_ctor_set(v___x_1275_, 1, v_snd_1224_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1299_ = _args[0];
lean_object* v_a_1300_ = _args[1];
lean_object* v_fst_1301_ = _args[2];
lean_object* v_a_1302_ = _args[3];
lean_object* v_lams_1303_ = _args[4];
lean_object* v_____r_1304_ = _args[5];
lean_object* v___y_1305_ = _args[6];
lean_object* v___y_1306_ = _args[7];
lean_object* v___y_1307_ = _args[8];
lean_object* v___y_1308_ = _args[9];
lean_object* v___y_1309_ = _args[10];
lean_object* v___y_1310_ = _args[11];
lean_object* v___y_1311_ = _args[12];
lean_object* v___y_1312_ = _args[13];
lean_object* v___y_1313_ = _args[14];
lean_object* v___y_1314_ = _args[15];
lean_object* v___y_1315_ = _args[16];
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1299_, v_a_1300_, v_fst_1301_, v_a_1302_, v_lams_1303_, v_____r_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v_lams_1303_);
lean_dec_ref(v_a_1302_);
lean_dec_ref(v_a_1300_);
return v_res_1316_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1323_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1324_ = l_Lean_Name_append(v___x_1323_, v___x_1322_);
return v___x_1324_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1327_ = l_Lean_stringToMessageData(v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_lams_1330_, lean_object* v_a_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___y_1344_; lean_object* v_toCold_1364_; lean_object* v_options_1365_; lean_object* v_fst_1366_; lean_object* v_snd_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1404_; 
v_toCold_1364_ = lean_ctor_get(v___y_1340_, 0);
v_options_1365_ = lean_ctor_get(v_toCold_1364_, 2);
v_fst_1366_ = lean_ctor_get(v_a_1331_, 0);
v_snd_1367_ = lean_ctor_get(v_a_1331_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_a_1331_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1369_ = v_a_1331_;
v_isShared_1370_ = v_isSharedCheck_1404_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snd_1367_);
lean_inc(v_fst_1366_);
lean_dec(v_a_1331_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1404_;
goto v_resetjp_1368_;
}
v___jp_1343_:
{
if (lean_obj_tag(v___y_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1355_; 
v_a_1345_ = lean_ctor_get(v___y_1344_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___y_1344_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1347_ = v___y_1344_;
v_isShared_1348_ = v_isSharedCheck_1355_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___y_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1355_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
if (lean_obj_tag(v_a_1345_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; 
v_a_1349_ = lean_ctor_get(v_a_1345_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v_a_1345_, 1);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v_a_1349_);
v___x_1351_ = v___x_1347_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
else
{
lean_object* v_a_1353_; 
lean_del_object(v___x_1347_);
v_a_1353_ = lean_ctor_get(v_a_1345_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v_a_1345_, 1);
v_a_1331_ = v_a_1353_;
goto _start;
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_a_1356_ = lean_ctor_get(v___y_1344_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___y_1344_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___y_1344_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___y_1344_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
v_resetjp_1368_:
{
lean_object* v_inheritedTraceOptions_1371_; uint8_t v_hasTrace_1372_; 
v_inheritedTraceOptions_1371_ = lean_ctor_get(v_toCold_1364_, 11);
v_hasTrace_1372_ = lean_ctor_get_uint8(v_options_1365_, sizeof(void*)*1);
if (v_hasTrace_1372_ == 0)
{
lean_del_object(v___x_1369_);
goto v___jp_1373_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1376_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1377_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1378_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1371_, v_options_1365_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_del_object(v___x_1369_);
goto v___jp_1373_;
}
else
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Meta_Grind_updateLastTag(v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec_ref_known(v___x_1379_, 1);
v___x_1380_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1367_);
v___x_1381_ = l_Lean_MessageData_ofExpr(v_snd_1367_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 7);
lean_ctor_set(v___x_1369_, 1, v___x_1381_);
lean_ctor_set(v___x_1369_, 0, v___x_1380_);
v___x_1383_ = v___x_1369_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1376_, v___x_1383_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1367_, v_a_1328_, v_fst_1366_, v_a_1329_, v_lams_1330_, v_a_1385_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
v___y_1344_ = v___x_1386_;
goto v___jp_1343_;
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_snd_1367_);
lean_dec(v_fst_1366_);
v_a_1387_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1384_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1384_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_del_object(v___x_1369_);
lean_dec(v_snd_1367_);
lean_dec(v_fst_1366_);
v_a_1396_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1379_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1379_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
v___jp_1373_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1367_, v_a_1328_, v_fst_1366_, v_a_1329_, v_lams_1330_, v___x_1374_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
v___y_1344_ = v___x_1375_;
goto v___jp_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_lams_1407_, lean_object* v_a_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1405_, v_a_1406_, v_lams_1407_, v_a_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v_lams_1407_);
lean_dec_ref(v_a_1406_);
lean_dec_ref(v_a_1405_);
return v_res_1420_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1425_ = l_Lean_stringToMessageData(v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1426_, lean_object* v_lams_1427_, lean_object* v_as_x27_1428_, lean_object* v_b_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
if (lean_obj_tag(v_as_x27_1428_) == 0)
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_b_1429_);
return v___x_1441_;
}
else
{
lean_object* v_toCold_1442_; lean_object* v_options_1443_; lean_object* v_head_1444_; lean_object* v_tail_1445_; lean_object* v_inheritedTraceOptions_1446_; uint8_t v_hasTrace_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; 
v_toCold_1442_ = lean_ctor_get(v___y_1438_, 0);
v_options_1443_ = lean_ctor_get(v_toCold_1442_, 2);
v_head_1444_ = lean_ctor_get(v_as_x27_1428_, 0);
v_tail_1445_ = lean_ctor_get(v_as_x27_1428_, 1);
v_inheritedTraceOptions_1446_ = lean_ctor_get(v_toCold_1442_, 11);
v_hasTrace_1447_ = lean_ctor_get_uint8(v_options_1443_, sizeof(void*)*1);
v___x_1448_ = lean_box(0);
v___x_1449_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1447_ == 0)
{
v___y_1451_ = v___y_1430_;
v___y_1452_ = v___y_1431_;
v___y_1453_ = v___y_1432_;
v___y_1454_ = v___y_1433_;
v___y_1455_ = v___y_1434_;
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1473_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1474_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1446_, v_options_1443_, v___x_1473_);
if (v___x_1474_ == 0)
{
v___y_1451_ = v___y_1430_;
v___y_1452_ = v___y_1431_;
v___y_1453_ = v___y_1432_;
v___y_1454_ = v___y_1433_;
v___y_1455_ = v___y_1434_;
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_Meta_Grind_updateLastTag(v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref_known(v___x_1475_, 1);
v___x_1476_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1444_);
v___x_1477_ = l_Lean_MessageData_ofExpr(v_head_1444_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1472_, v___x_1478_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_dec_ref_known(v___x_1479_, 1);
v___y_1451_ = v___y_1430_;
v___y_1452_ = v___y_1431_;
v___y_1453_ = v___y_1432_;
v___y_1454_ = v___y_1433_;
v___y_1455_ = v___y_1434_;
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
goto v___jp_1450_;
}
else
{
return v___x_1479_;
}
}
else
{
return v___x_1475_;
}
}
}
v___jp_1450_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_inc(v_head_1444_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1449_);
lean_ctor_set(v___x_1461_, 1, v_head_1444_);
v___x_1462_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1444_, v_a_1426_, v_lams_1427_, v___x_1461_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_dec_ref_known(v___x_1462_, 1);
v_as_x27_1428_ = v_tail_1445_;
v_b_1429_ = v___x_1448_;
goto _start;
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_a_1464_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1462_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1462_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1480_, lean_object* v_lams_1481_, lean_object* v_as_x27_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1480_, v_lams_1481_, v_as_x27_1482_, v_b_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec(v_as_x27_1482_);
lean_dec_ref(v_lams_1481_);
lean_dec_ref(v_a_1480_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1496_, lean_object* v_lams_1497_, lean_object* v_as_1498_, lean_object* v_as_x27_1499_, lean_object* v_b_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
if (lean_obj_tag(v_as_x27_1499_) == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_b_1500_);
return v___x_1512_;
}
else
{
lean_object* v_toCold_1513_; lean_object* v_options_1514_; lean_object* v_head_1515_; lean_object* v_tail_1516_; lean_object* v_inheritedTraceOptions_1517_; uint8_t v_hasTrace_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; 
v_toCold_1513_ = lean_ctor_get(v___y_1509_, 0);
v_options_1514_ = lean_ctor_get(v_toCold_1513_, 2);
v_head_1515_ = lean_ctor_get(v_as_x27_1499_, 0);
v_tail_1516_ = lean_ctor_get(v_as_x27_1499_, 1);
v_inheritedTraceOptions_1517_ = lean_ctor_get(v_toCold_1513_, 11);
v_hasTrace_1518_ = lean_ctor_get_uint8(v_options_1514_, sizeof(void*)*1);
v___x_1519_ = lean_box(0);
v___x_1520_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1518_ == 0)
{
v___y_1522_ = v___y_1501_;
v___y_1523_ = v___y_1502_;
v___y_1524_ = v___y_1503_;
v___y_1525_ = v___y_1504_;
v___y_1526_ = v___y_1505_;
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1543_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1544_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1545_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1517_, v_options_1514_, v___x_1544_);
if (v___x_1545_ == 0)
{
v___y_1522_ = v___y_1501_;
v___y_1523_ = v___y_1502_;
v___y_1524_ = v___y_1503_;
v___y_1525_ = v___y_1504_;
v___y_1526_ = v___y_1505_;
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Meta_Grind_updateLastTag(v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec_ref_known(v___x_1546_, 1);
v___x_1547_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1515_);
v___x_1548_ = l_Lean_MessageData_ofExpr(v_head_1515_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1543_, v___x_1549_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_dec_ref_known(v___x_1550_, 1);
v___y_1522_ = v___y_1501_;
v___y_1523_ = v___y_1502_;
v___y_1524_ = v___y_1503_;
v___y_1525_ = v___y_1504_;
v___y_1526_ = v___y_1505_;
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
goto v___jp_1521_;
}
else
{
return v___x_1550_;
}
}
else
{
return v___x_1546_;
}
}
}
v___jp_1521_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_inc(v_head_1515_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1520_);
lean_ctor_set(v___x_1532_, 1, v_head_1515_);
v___x_1533_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1515_, v_a_1496_, v_lams_1497_, v___x_1532_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1534_; 
lean_dec_ref_known(v___x_1533_, 1);
v___x_1534_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1496_, v_lams_1497_, v_tail_1516_, v___x_1519_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1534_;
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_a_1535_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1533_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1533_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1551_, lean_object* v_lams_1552_, lean_object* v_as_1553_, lean_object* v_as_x27_1554_, lean_object* v_b_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1551_, v_lams_1552_, v_as_1553_, v_as_x27_1554_, v_b_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec(v_as_x27_1554_);
lean_dec(v_as_1553_);
lean_dec_ref(v_lams_1552_);
lean_dec_ref(v_a_1551_);
return v_res_1567_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
return v___x_1570_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1573_ = l_Lean_stringToMessageData(v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1574_, lean_object* v_lams_1575_, lean_object* v_as_1576_, size_t v_sz_1577_, size_t v_i_1578_, lean_object* v_b_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_usize_dec_lt(v_i_1578_, v_sz_1577_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v_b_1579_);
return v___x_1592_;
}
else
{
lean_object* v_toCold_1593_; lean_object* v_options_1594_; lean_object* v_inheritedTraceOptions_1595_; uint8_t v_hasTrace_1596_; lean_object* v___x_1597_; lean_object* v_a_1598_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; 
v_toCold_1593_ = lean_ctor_get(v___y_1588_, 0);
v_options_1594_ = lean_ctor_get(v_toCold_1593_, 2);
v_inheritedTraceOptions_1595_ = lean_ctor_get(v_toCold_1593_, 11);
v_hasTrace_1596_ = lean_ctor_get_uint8(v_options_1594_, sizeof(void*)*1);
v___x_1597_ = lean_box(0);
v_a_1598_ = lean_array_uget_borrowed(v_as_1576_, v_i_1578_);
if (v_hasTrace_1596_ == 0)
{
v___y_1600_ = v___y_1580_;
v___y_1601_ = v___y_1581_;
v___y_1602_ = v___y_1582_;
v___y_1603_ = v___y_1583_;
v___y_1604_ = v___y_1584_;
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1625_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1626_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1627_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1595_, v_options_1594_, v___x_1626_);
if (v___x_1627_ == 0)
{
v___y_1600_ = v___y_1580_;
v___y_1601_ = v___y_1581_;
v___y_1602_ = v___y_1582_;
v___y_1603_ = v___y_1583_;
v___y_1604_ = v___y_1584_;
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Meta_Grind_updateLastTag(v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v___x_1629_; 
lean_dec_ref_known(v___x_1628_, 1);
v___x_1629_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1598_, v___y_1580_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1598_);
v___x_1632_ = l_Lean_MessageData_ofExpr(v_a_1598_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1630_);
lean_dec(v_a_1630_);
v___x_1637_ = lean_box(0);
v___x_1638_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1636_, v___x_1637_);
v___x_1639_ = l_Lean_MessageData_ofList(v___x_1638_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1635_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1625_, v___x_1640_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_dec_ref_known(v___x_1641_, 1);
v___y_1600_ = v___y_1580_;
v___y_1601_ = v___y_1581_;
v___y_1602_ = v___y_1582_;
v___y_1603_ = v___y_1583_;
v___y_1604_ = v___y_1584_;
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
goto v___jp_1599_;
}
else
{
return v___x_1641_;
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_a_1642_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1629_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1629_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
return v___x_1628_;
}
}
}
v___jp_1599_:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1598_, v___y_1600_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1611_);
lean_dec(v_a_1611_);
v___x_1613_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1574_, v_lams_1575_, v___x_1612_, v___x_1612_, v___x_1597_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___x_1612_);
if (lean_obj_tag(v___x_1613_) == 0)
{
size_t v___x_1614_; size_t v___x_1615_; 
lean_dec_ref_known(v___x_1613_, 1);
v___x_1614_ = ((size_t)1ULL);
v___x_1615_ = lean_usize_add(v_i_1578_, v___x_1614_);
v_i_1578_ = v___x_1615_;
v_b_1579_ = v___x_1597_;
goto _start;
}
else
{
return v___x_1613_;
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_a_1617_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1610_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1610_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1650_ = _args[0];
lean_object* v_lams_1651_ = _args[1];
lean_object* v_as_1652_ = _args[2];
lean_object* v_sz_1653_ = _args[3];
lean_object* v_i_1654_ = _args[4];
lean_object* v_b_1655_ = _args[5];
lean_object* v___y_1656_ = _args[6];
lean_object* v___y_1657_ = _args[7];
lean_object* v___y_1658_ = _args[8];
lean_object* v___y_1659_ = _args[9];
lean_object* v___y_1660_ = _args[10];
lean_object* v___y_1661_ = _args[11];
lean_object* v___y_1662_ = _args[12];
lean_object* v___y_1663_ = _args[13];
lean_object* v___y_1664_ = _args[14];
lean_object* v___y_1665_ = _args[15];
lean_object* v___y_1666_ = _args[16];
_start:
{
size_t v_sz_boxed_1667_; size_t v_i_boxed_1668_; lean_object* v_res_1669_; 
v_sz_boxed_1667_ = lean_unbox_usize(v_sz_1653_);
lean_dec(v_sz_1653_);
v_i_boxed_1668_ = lean_unbox_usize(v_i_1654_);
lean_dec(v_i_1654_);
v_res_1669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1650_, v_lams_1651_, v_as_1652_, v_sz_boxed_1667_, v_i_boxed_1668_, v_b_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v_as_1652_);
lean_dec_ref(v_lams_1651_);
lean_dec_ref(v_a_1650_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1670_, lean_object* v_lams_1671_, lean_object* v_as_1672_, size_t v_sz_1673_, size_t v_i_1674_, lean_object* v_b_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_usize_dec_lt(v_i_1674_, v_sz_1673_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v_b_1675_);
return v___x_1688_;
}
else
{
lean_object* v_toCold_1689_; lean_object* v_options_1690_; lean_object* v_inheritedTraceOptions_1691_; uint8_t v_hasTrace_1692_; lean_object* v___x_1693_; lean_object* v_a_1694_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; 
v_toCold_1689_ = lean_ctor_get(v___y_1684_, 0);
v_options_1690_ = lean_ctor_get(v_toCold_1689_, 2);
v_inheritedTraceOptions_1691_ = lean_ctor_get(v_toCold_1689_, 11);
v_hasTrace_1692_ = lean_ctor_get_uint8(v_options_1690_, sizeof(void*)*1);
v___x_1693_ = lean_box(0);
v_a_1694_ = lean_array_uget_borrowed(v_as_1672_, v_i_1674_);
if (v_hasTrace_1692_ == 0)
{
v___y_1696_ = v___y_1676_;
v___y_1697_ = v___y_1677_;
v___y_1698_ = v___y_1678_;
v___y_1699_ = v___y_1679_;
v___y_1700_ = v___y_1680_;
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
goto v___jp_1695_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1721_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1722_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1723_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1691_, v_options_1690_, v___x_1722_);
if (v___x_1723_ == 0)
{
v___y_1696_ = v___y_1676_;
v___y_1697_ = v___y_1677_;
v___y_1698_ = v___y_1678_;
v___y_1699_ = v___y_1679_;
v___y_1700_ = v___y_1680_;
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
goto v___jp_1695_;
}
else
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_Meta_Grind_updateLastTag(v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref_known(v___x_1724_, 1);
v___x_1725_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1694_, v___y_1676_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1694_);
v___x_1728_ = l_Lean_MessageData_ofExpr(v_a_1694_);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1726_);
lean_dec(v_a_1726_);
v___x_1733_ = lean_box(0);
v___x_1734_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1732_, v___x_1733_);
v___x_1735_ = l_Lean_MessageData_ofList(v___x_1734_);
v___x_1736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1731_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1721_, v___x_1736_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_dec_ref_known(v___x_1737_, 1);
v___y_1696_ = v___y_1676_;
v___y_1697_ = v___y_1677_;
v___y_1698_ = v___y_1678_;
v___y_1699_ = v___y_1679_;
v___y_1700_ = v___y_1680_;
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
goto v___jp_1695_;
}
else
{
return v___x_1737_;
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
v_a_1738_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1725_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1725_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
return v___x_1724_;
}
}
}
v___jp_1695_:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1694_, v___y_1696_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v___x_1708_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1707_);
lean_dec(v_a_1707_);
v___x_1709_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1670_, v_lams_1671_, v___x_1708_, v___x_1708_, v___x_1693_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___x_1708_);
if (lean_obj_tag(v___x_1709_) == 0)
{
size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
lean_dec_ref_known(v___x_1709_, 1);
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1674_, v___x_1710_);
v___x_1712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1670_, v_lams_1671_, v_as_1672_, v_sz_1673_, v___x_1711_, v___x_1693_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
return v___x_1712_;
}
else
{
return v___x_1709_;
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_a_1713_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1706_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1706_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1746_ = _args[0];
lean_object* v_lams_1747_ = _args[1];
lean_object* v_as_1748_ = _args[2];
lean_object* v_sz_1749_ = _args[3];
lean_object* v_i_1750_ = _args[4];
lean_object* v_b_1751_ = _args[5];
lean_object* v___y_1752_ = _args[6];
lean_object* v___y_1753_ = _args[7];
lean_object* v___y_1754_ = _args[8];
lean_object* v___y_1755_ = _args[9];
lean_object* v___y_1756_ = _args[10];
lean_object* v___y_1757_ = _args[11];
lean_object* v___y_1758_ = _args[12];
lean_object* v___y_1759_ = _args[13];
lean_object* v___y_1760_ = _args[14];
lean_object* v___y_1761_ = _args[15];
lean_object* v___y_1762_ = _args[16];
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1749_);
lean_dec(v_sz_1749_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1750_);
lean_dec(v_i_1750_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1746_, v_lams_1747_, v_as_1748_, v_sz_boxed_1763_, v_i_boxed_1764_, v_b_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v_as_1748_);
lean_dec_ref(v_lams_1747_);
lean_dec_ref(v_a_1746_);
return v_res_1765_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1768_ = l_Lean_stringToMessageData(v___x_1767_);
return v___x_1768_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1771_ = l_Lean_stringToMessageData(v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1772_, lean_object* v_fns_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1785_ = lean_array_get_size(v_lams_1772_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_nat_dec_eq(v___x_1785_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1788_ = l_Lean_instInhabitedExpr;
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = lean_nat_sub(v___x_1785_, v___x_1789_);
v___x_1791_ = lean_array_get_borrowed(v___x_1788_, v_lams_1772_, v___x_1790_);
lean_dec(v___x_1790_);
v___x_1792_ = lean_st_ref_get(v_a_1774_);
lean_inc(v___x_1791_);
v___x_1793_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1792_, v___x_1791_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec(v___x_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v_toCold_1818_; lean_object* v_options_1819_; uint8_t v_hasTrace_1820_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref_known(v___x_1793_, 1);
v_toCold_1818_ = lean_ctor_get(v_a_1782_, 0);
v_options_1819_ = lean_ctor_get(v_toCold_1818_, 2);
v_hasTrace_1820_ = lean_ctor_get_uint8(v_options_1819_, sizeof(void*)*1);
if (v_hasTrace_1820_ == 0)
{
v___y_1796_ = v_a_1774_;
v___y_1797_ = v_a_1775_;
v___y_1798_ = v_a_1776_;
v___y_1799_ = v_a_1777_;
v___y_1800_ = v_a_1778_;
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
goto v___jp_1795_;
}
else
{
lean_object* v_inheritedTraceOptions_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v_inheritedTraceOptions_1821_ = lean_ctor_get(v_toCold_1818_, 11);
v___x_1822_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1823_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1824_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1821_, v_options_1819_, v___x_1823_);
if (v___x_1824_ == 0)
{
v___y_1796_ = v_a_1774_;
v___y_1797_ = v_a_1775_;
v___y_1798_ = v_a_1776_;
v___y_1799_ = v_a_1777_;
v___y_1800_ = v_a_1778_;
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Meta_Grind_updateLastTag(v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec_ref_known(v___x_1825_, 1);
v___x_1826_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1773_);
v___x_1827_ = lean_array_to_list(v_fns_1773_);
v___x_1828_ = lean_box(0);
v___x_1829_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1827_, v___x_1828_);
v___x_1830_ = l_Lean_MessageData_ofList(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1826_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
lean_inc_ref(v_lams_1772_);
v___x_1834_ = lean_array_to_list(v_lams_1772_);
v___x_1835_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1834_, v___x_1828_);
v___x_1836_ = l_Lean_MessageData_ofList(v___x_1835_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1833_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1822_, v___x_1837_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_dec_ref_known(v___x_1838_, 1);
v___y_1796_ = v_a_1774_;
v___y_1797_ = v_a_1775_;
v___y_1798_ = v_a_1776_;
v___y_1799_ = v_a_1777_;
v___y_1800_ = v_a_1778_;
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
goto v___jp_1795_;
}
else
{
lean_dec(v_a_1794_);
lean_dec_ref(v_fns_1773_);
lean_dec_ref(v_lams_1772_);
return v___x_1838_;
}
}
else
{
lean_dec(v_a_1794_);
lean_dec_ref(v_fns_1773_);
lean_dec_ref(v_lams_1772_);
return v___x_1825_;
}
}
}
v___jp_1795_:
{
lean_object* v___x_1806_; size_t v_sz_1807_; size_t v___x_1808_; lean_object* v___x_1809_; 
v___x_1806_ = lean_box(0);
v_sz_1807_ = lean_array_size(v_fns_1773_);
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1794_, v_lams_1772_, v_fns_1773_, v_sz_1807_, v___x_1808_, v___x_1806_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec_ref(v_fns_1773_);
lean_dec_ref(v_lams_1772_);
lean_dec(v_a_1794_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v___x_1809_, 0);
lean_dec(v_unused_1817_);
v___x_1811_ = v___x_1809_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v___x_1809_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1806_);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1806_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
return v___x_1809_;
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v_fns_1773_);
lean_dec_ref(v_lams_1772_);
v_a_1839_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1793_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1793_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec_ref(v_fns_1773_);
lean_dec_ref(v_lams_1772_);
v___x_1847_ = lean_box(0);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1849_, lean_object* v_fns_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1849_, v_fns_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec(v_a_1851_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_lams_1865_, lean_object* v_inst_1866_, lean_object* v_a_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1863_, v_a_1864_, v_lams_1865_, v_a_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_lams_1882_, lean_object* v_inst_1883_, lean_object* v_a_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1880_, v_a_1881_, v_lams_1882_, v_inst_1883_, v_a_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v_lams_1882_);
lean_dec_ref(v_a_1881_);
lean_dec_ref(v_a_1880_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1897_, lean_object* v_lams_1898_, lean_object* v_as_1899_, lean_object* v_as_x27_1900_, lean_object* v_b_1901_, lean_object* v_a_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1897_, v_lams_1898_, v_as_1899_, v_as_x27_1900_, v_b_1901_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1915_ = _args[0];
lean_object* v_lams_1916_ = _args[1];
lean_object* v_as_1917_ = _args[2];
lean_object* v_as_x27_1918_ = _args[3];
lean_object* v_b_1919_ = _args[4];
lean_object* v_a_1920_ = _args[5];
lean_object* v___y_1921_ = _args[6];
lean_object* v___y_1922_ = _args[7];
lean_object* v___y_1923_ = _args[8];
lean_object* v___y_1924_ = _args[9];
lean_object* v___y_1925_ = _args[10];
lean_object* v___y_1926_ = _args[11];
lean_object* v___y_1927_ = _args[12];
lean_object* v___y_1928_ = _args[13];
lean_object* v___y_1929_ = _args[14];
lean_object* v___y_1930_ = _args[15];
lean_object* v___y_1931_ = _args[16];
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1915_, v_lams_1916_, v_as_1917_, v_as_x27_1918_, v_b_1919_, v_a_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec(v_as_x27_1918_);
lean_dec(v_as_1917_);
lean_dec_ref(v_lams_1916_);
lean_dec_ref(v_a_1915_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1933_, lean_object* v_lams_1934_, lean_object* v_as_1935_, lean_object* v_as_x27_1936_, lean_object* v_b_1937_, lean_object* v_a_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1933_, v_lams_1934_, v_as_x27_1936_, v_b_1937_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1951_ = _args[0];
lean_object* v_lams_1952_ = _args[1];
lean_object* v_as_1953_ = _args[2];
lean_object* v_as_x27_1954_ = _args[3];
lean_object* v_b_1955_ = _args[4];
lean_object* v_a_1956_ = _args[5];
lean_object* v___y_1957_ = _args[6];
lean_object* v___y_1958_ = _args[7];
lean_object* v___y_1959_ = _args[8];
lean_object* v___y_1960_ = _args[9];
lean_object* v___y_1961_ = _args[10];
lean_object* v___y_1962_ = _args[11];
lean_object* v___y_1963_ = _args[12];
lean_object* v___y_1964_ = _args[13];
lean_object* v___y_1965_ = _args[14];
lean_object* v___y_1966_ = _args[15];
lean_object* v___y_1967_ = _args[16];
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1951_, v_lams_1952_, v_as_1953_, v_as_x27_1954_, v_b_1955_, v_a_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v_as_x27_1954_);
lean_dec(v_as_1953_);
lean_dec_ref(v_lams_1952_);
lean_dec_ref(v_a_1951_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1972_, lean_object* v_as_1973_, size_t v_sz_1974_, size_t v_i_1975_, lean_object* v_b_1976_){
_start:
{
lean_object* v_a_1978_; uint8_t v___x_1982_; 
v___x_1982_ = lean_usize_dec_lt(v_i_1975_, v_sz_1974_);
if (v___x_1982_ == 0)
{
lean_inc_ref(v_b_1976_);
return v_b_1976_;
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v_a_1985_; 
v___x_1983_ = lean_box(0);
v___x_1984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1985_ = lean_array_uget_borrowed(v_as_1973_, v_i_1975_);
if (lean_obj_tag(v_a_1985_) == 6)
{
lean_object* v_binderType_1986_; size_t v___x_1987_; size_t v___x_1988_; uint8_t v___x_1989_; 
v_binderType_1986_ = lean_ctor_get(v_a_1985_, 1);
v___x_1987_ = lean_ptr_addr(v_d_1972_);
v___x_1988_ = lean_ptr_addr(v_binderType_1986_);
v___x_1989_ = lean_usize_dec_eq(v___x_1987_, v___x_1988_);
if (v___x_1989_ == 0)
{
v_a_1978_ = v___x_1984_;
goto v___jp_1977_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_inc_ref(v_a_1985_);
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v_a_1985_);
v___x_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v___x_1983_);
return v___x_1992_;
}
}
else
{
v_a_1978_ = v___x_1984_;
goto v___jp_1977_;
}
}
v___jp_1977_:
{
size_t v___x_1979_; size_t v___x_1980_; 
v___x_1979_ = ((size_t)1ULL);
v___x_1980_ = lean_usize_add(v_i_1975_, v___x_1979_);
v_i_1975_ = v___x_1980_;
v_b_1976_ = v_a_1978_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_1993_, lean_object* v_as_1994_, lean_object* v_sz_1995_, lean_object* v_i_1996_, lean_object* v_b_1997_){
_start:
{
size_t v_sz_boxed_1998_; size_t v_i_boxed_1999_; lean_object* v_res_2000_; 
v_sz_boxed_1998_ = lean_unbox_usize(v_sz_1995_);
lean_dec(v_sz_1995_);
v_i_boxed_1999_ = lean_unbox_usize(v_i_1996_);
lean_dec(v_i_1996_);
v_res_2000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1993_, v_as_1994_, v_sz_boxed_1998_, v_i_boxed_1999_, v_b_1997_);
lean_dec_ref(v_b_1997_);
lean_dec_ref(v_as_1994_);
lean_dec_ref(v_d_1993_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2001_, lean_object* v_d_2002_){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; size_t v_sz_2005_; size_t v___x_2006_; lean_object* v___x_2007_; lean_object* v_fst_2008_; 
v___x_2003_ = lean_box(0);
v___x_2004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2005_ = lean_array_size(v_lams_2001_);
v___x_2006_ = ((size_t)0ULL);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2002_, v_lams_2001_, v_sz_2005_, v___x_2006_, v___x_2004_);
v_fst_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_fst_2008_);
lean_dec_ref(v___x_2007_);
if (lean_obj_tag(v_fst_2008_) == 0)
{
return v___x_2003_;
}
else
{
lean_object* v_val_2009_; 
v_val_2009_ = lean_ctor_get(v_fst_2008_, 0);
lean_inc(v_val_2009_);
lean_dec_ref_known(v_fst_2008_, 1);
return v_val_2009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2010_, lean_object* v_d_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2010_, v_d_2011_);
lean_dec_ref(v_d_2011_);
lean_dec_ref(v_lams_2010_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2023_, lean_object* v_lams_u2081_2024_, lean_object* v_as_2025_, size_t v_sz_2026_, size_t v_i_2027_, lean_object* v_b_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_a_2041_; uint8_t v___x_2045_; 
v___x_2045_ = lean_usize_dec_lt(v_i_2027_, v_sz_2026_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_b_2028_);
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; lean_object* v_a_2048_; 
v___x_2047_ = lean_box(0);
v_a_2048_ = lean_array_uget_borrowed(v_as_2025_, v_i_2027_);
if (lean_obj_tag(v_a_2048_) == 6)
{
lean_object* v_binderType_2049_; lean_object* v_body_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_binderType_2049_ = lean_ctor_get(v_a_2048_, 1);
v_body_2050_ = lean_ctor_get(v_a_2048_, 2);
v___x_2051_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_binderType_2049_);
v___x_2052_ = l_Lean_Meta_getLevel(v_binderType_2049_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
v___x_2054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2056_, 0, v_a_2053_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
lean_inc_ref(v___x_2056_);
v___x_2057_ = l_Lean_mkConst(v___x_2054_, v___x_2056_);
lean_inc_ref(v_binderType_2049_);
v___x_2058_ = l_Lean_Expr_app___override(v___x_2057_, v_binderType_2049_);
v___x_2059_ = lean_box(0);
v___x_2060_ = l_Lean_Meta_synthInstance_x3f(v___x_2058_, v___x_2059_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
if (lean_obj_tag(v_a_2061_) == 1)
{
lean_object* v_val_2062_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; uint8_t v___x_2127_; 
v_val_2062_ = lean_ctor_get(v_a_2061_, 0);
lean_inc(v_val_2062_);
lean_dec_ref_known(v_a_2061_, 1);
v___x_2127_ = l_Lean_Expr_hasLooseBVars(v_body_2050_);
if (v___x_2127_ == 0)
{
v___y_2064_ = v___y_2029_;
v___y_2065_ = v___y_2030_;
v___y_2066_ = v___y_2031_;
v___y_2067_ = v___y_2032_;
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2056_);
v___x_2129_ = l_Lean_mkConst(v___x_2128_, v___x_2056_);
lean_inc_ref(v_binderType_2049_);
v___x_2130_ = l_Lean_Expr_app___override(v___x_2129_, v_binderType_2049_);
v___x_2131_ = l_Lean_Meta_synthInstance_x3f(v___x_2130_, v___x_2059_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
if (lean_obj_tag(v_a_2132_) == 0)
{
lean_dec(v_val_2062_);
lean_dec_ref_known(v___x_2056_, 2);
v_a_2041_ = v___x_2047_;
goto v___jp_2040_;
}
else
{
lean_dec_ref_known(v_a_2132_, 1);
if (v___x_2127_ == 0)
{
lean_dec(v_val_2062_);
lean_dec_ref_known(v___x_2056_, 2);
v_a_2041_ = v___x_2047_;
goto v___jp_2040_;
}
else
{
v___y_2064_ = v___y_2029_;
v___y_2065_ = v___y_2030_;
v___y_2066_ = v___y_2031_;
v___y_2067_ = v___y_2032_;
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
goto v___jp_2063_;
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_val_2062_);
lean_dec_ref_known(v___x_2056_, 2);
v_a_2133_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2131_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2131_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
v___jp_2063_:
{
lean_object* v___x_2074_; 
v___x_2074_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2023_, v_binderType_2049_);
if (lean_obj_tag(v___x_2074_) == 1)
{
lean_object* v_val_2075_; 
v_val_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v___x_2074_, 1);
if (lean_obj_tag(v_val_2075_) == 6)
{
lean_object* v_binderType_2076_; lean_object* v_body_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_binderType_2076_ = lean_ctor_get(v_val_2075_, 1);
lean_inc_ref(v_binderType_2076_);
v_body_2077_ = lean_ctor_get(v_val_2075_, 2);
lean_inc_ref(v_body_2077_);
lean_dec_ref_known(v_val_2075_, 3);
v___x_2078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2079_ = l_Lean_mkConst(v___x_2078_, v___x_2056_);
v___x_2080_ = l_Lean_mkAppB(v___x_2079_, v_binderType_2076_, v_val_2062_);
v___x_2081_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2080_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = lean_expr_instantiate1(v_body_2050_, v_a_2082_);
v___x_2084_ = lean_expr_instantiate1(v_body_2077_, v_a_2082_);
lean_dec_ref(v_body_2077_);
v___x_2085_ = lean_array_fget_borrowed(v_lams_u2081_2024_, v___x_2051_);
v___x_2086_ = lean_array_fget_borrowed(v_lams_u2082_2023_, v___x_2051_);
lean_inc(v___y_2073_);
lean_inc_ref(v___y_2072_);
lean_inc(v___y_2071_);
lean_inc_ref(v___y_2070_);
lean_inc(v___y_2069_);
lean_inc_ref(v___y_2068_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2066_);
lean_inc(v___y_2065_);
lean_inc(v___y_2064_);
lean_inc(v___x_2086_);
lean_inc(v___x_2085_);
v___x_2087_ = lean_grind_mk_eq_proof(v___x_2085_, v___x_2086_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = l_Lean_Meta_mkCongrFun(v_a_2088_, v_a_2082_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = l_Lean_Meta_mkEq(v___x_2083_, v___x_2084_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = l_Lean_Meta_mkExpectedPropHint(v_a_2090_, v_a_2092_);
v___x_2094_ = l_Lean_Meta_Grind_pushNewFact(v___x_2093_, v___x_2051_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_dec_ref_known(v___x_2094_, 1);
v_a_2041_ = v___x_2047_;
goto v___jp_2040_;
}
else
{
return v___x_2094_;
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec(v_a_2090_);
v_a_2095_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2091_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2091_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref(v___x_2084_);
lean_dec_ref(v___x_2083_);
v_a_2103_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2089_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2089_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v___x_2084_);
lean_dec_ref(v___x_2083_);
lean_dec(v_a_2082_);
v_a_2111_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2087_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2087_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v_body_2077_);
v_a_2119_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2081_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2081_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_dec(v_val_2075_);
lean_dec(v_val_2062_);
lean_dec_ref_known(v___x_2056_, 2);
v_a_2041_ = v___x_2047_;
goto v___jp_2040_;
}
}
else
{
lean_dec(v___x_2074_);
lean_dec(v_val_2062_);
lean_dec_ref_known(v___x_2056_, 2);
v_a_2041_ = v___x_2047_;
goto v___jp_2040_;
}
}
}
else
{
lean_dec(v_a_2061_);
lean_dec_ref_known(v___x_2056_, 2);
v_a_2041_ = v___x_2047_;
goto v___jp_2040_;
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref_known(v___x_2056_, 2);
v_a_2141_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2060_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2060_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
v_a_2149_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2052_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2052_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
v_a_2041_ = v___x_2047_;
goto v___jp_2040_;
}
}
v___jp_2040_:
{
size_t v___x_2042_; size_t v___x_2043_; 
v___x_2042_ = ((size_t)1ULL);
v___x_2043_ = lean_usize_add(v_i_2027_, v___x_2042_);
v_i_2027_ = v___x_2043_;
v_b_2028_ = v_a_2041_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2157_ = _args[0];
lean_object* v_lams_u2081_2158_ = _args[1];
lean_object* v_as_2159_ = _args[2];
lean_object* v_sz_2160_ = _args[3];
lean_object* v_i_2161_ = _args[4];
lean_object* v_b_2162_ = _args[5];
lean_object* v___y_2163_ = _args[6];
lean_object* v___y_2164_ = _args[7];
lean_object* v___y_2165_ = _args[8];
lean_object* v___y_2166_ = _args[9];
lean_object* v___y_2167_ = _args[10];
lean_object* v___y_2168_ = _args[11];
lean_object* v___y_2169_ = _args[12];
lean_object* v___y_2170_ = _args[13];
lean_object* v___y_2171_ = _args[14];
lean_object* v___y_2172_ = _args[15];
lean_object* v___y_2173_ = _args[16];
_start:
{
size_t v_sz_boxed_2174_; size_t v_i_boxed_2175_; lean_object* v_res_2176_; 
v_sz_boxed_2174_ = lean_unbox_usize(v_sz_2160_);
lean_dec(v_sz_2160_);
v_i_boxed_2175_ = lean_unbox_usize(v_i_2161_);
lean_dec(v_i_2161_);
v_res_2176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2157_, v_lams_u2081_2158_, v_as_2159_, v_sz_boxed_2174_, v_i_boxed_2175_, v_b_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
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
lean_dec_ref(v_lams_u2081_2158_);
lean_dec_ref(v_lams_u2082_2157_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2177_, lean_object* v_lams_u2082_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2190_ = lean_array_get_size(v_lams_u2081_2177_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_nat_dec_eq(v___x_2190_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = lean_array_get_size(v_lams_u2082_2178_);
v___x_2194_ = lean_nat_dec_eq(v___x_2193_, v___x_2191_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; size_t v_sz_2196_; size_t v___x_2197_; lean_object* v___x_2198_; 
v___x_2195_ = lean_box(0);
v_sz_2196_ = lean_array_size(v_lams_u2081_2177_);
v___x_2197_ = ((size_t)0ULL);
v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2178_, v_lams_u2081_2177_, v_lams_u2081_2177_, v_sz_2196_, v___x_2197_, v___x_2195_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; 
v_unused_2206_ = lean_ctor_get(v___x_2198_, 0);
lean_dec(v_unused_2206_);
v___x_2200_ = v___x_2198_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_dec(v___x_2198_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2195_);
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2195_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
else
{
return v___x_2198_;
}
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = lean_box(0);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2211_, lean_object* v_lams_u2082_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2211_, v_lams_u2082_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec_ref(v_lams_u2082_2212_);
lean_dec_ref(v_lams_u2081_2211_);
return v_res_2224_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2225_){
_start:
{
uint8_t v___x_2226_; 
v___x_2226_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2227_){
_start:
{
uint8_t v_res_2228_; lean_object* v_r_2229_; 
v_res_2228_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2227_);
lean_dec_ref(v_x_2227_);
v_r_2229_ = lean_box(v_res_2228_);
return v_r_2229_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2230_, lean_object* v_x_2231_){
_start:
{
uint8_t v___x_2232_; 
v___x_2232_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2233_, lean_object* v_x_2234_){
_start:
{
uint8_t v_res_2235_; lean_object* v_r_2236_; 
v_res_2235_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2233_, v_x_2234_);
lean_dec_ref(v_x_2234_);
v_r_2236_ = lean_box(v_res_2235_);
return v_r_2236_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2237_, lean_object* v_v_2238_, lean_object* v_i_2239_){
_start:
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = lean_array_get_size(v_xs_2237_);
v___x_2241_ = lean_nat_dec_lt(v_i_2239_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_dec(v_i_2239_);
v___x_2242_ = lean_box(0);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; size_t v___x_2244_; size_t v___x_2245_; uint8_t v___x_2246_; 
v___x_2243_ = lean_array_fget_borrowed(v_xs_2237_, v_i_2239_);
v___x_2244_ = lean_ptr_addr(v___x_2243_);
v___x_2245_ = lean_ptr_addr(v_v_2238_);
v___x_2246_ = lean_usize_dec_eq(v___x_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = lean_nat_add(v_i_2239_, v___x_2247_);
lean_dec(v_i_2239_);
v_i_2239_ = v___x_2248_;
goto _start;
}
else
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2250_, 0, v_i_2239_);
return v___x_2250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2251_, lean_object* v_v_2252_, lean_object* v_i_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2251_, v_v_2252_, v_i_2253_);
lean_dec_ref(v_v_2252_);
lean_dec_ref(v_xs_2251_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2255_, lean_object* v_v_2256_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_unsigned_to_nat(0u);
v___x_2258_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2255_, v_v_2256_, v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2259_, lean_object* v_v_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2259_, v_v_2260_);
lean_dec_ref(v_v_2260_);
lean_dec_ref(v_xs_2259_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2262_, size_t v_x_2263_, lean_object* v_x_2264_){
_start:
{
if (lean_obj_tag(v_x_2262_) == 0)
{
lean_object* v_es_2265_; lean_object* v___x_2266_; size_t v___x_2267_; size_t v___x_2268_; lean_object* v_j_2269_; lean_object* v_entry_2270_; 
v_es_2265_ = lean_ctor_get(v_x_2262_, 0);
v___x_2266_ = lean_box(2);
v___x_2267_ = ((size_t)31ULL);
v___x_2268_ = lean_usize_land(v_x_2263_, v___x_2267_);
v_j_2269_ = lean_usize_to_nat(v___x_2268_);
v_entry_2270_ = lean_array_get(v___x_2266_, v_es_2265_, v_j_2269_);
switch(lean_obj_tag(v_entry_2270_))
{
case 0:
{
lean_object* v_key_2271_; size_t v___x_2272_; size_t v___x_2273_; uint8_t v___x_2274_; 
v_key_2271_ = lean_ctor_get(v_entry_2270_, 0);
lean_inc(v_key_2271_);
lean_dec_ref_known(v_entry_2270_, 2);
v___x_2272_ = lean_ptr_addr(v_x_2264_);
v___x_2273_ = lean_ptr_addr(v_key_2271_);
lean_dec(v_key_2271_);
v___x_2274_ = lean_usize_dec_eq(v___x_2272_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_dec(v_j_2269_);
return v_x_2262_;
}
else
{
lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2282_; 
lean_inc_ref(v_es_2265_);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_x_2262_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v_x_2262_, 0);
lean_dec(v_unused_2283_);
v___x_2276_ = v_x_2262_;
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
else
{
lean_dec(v_x_2262_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = lean_array_set(v_es_2265_, v_j_2269_, v___x_2266_);
lean_dec(v_j_2269_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 0, v___x_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
case 1:
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2318_; 
lean_inc_ref(v_es_2265_);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_x_2262_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; 
v_unused_2319_ = lean_ctor_get(v_x_2262_, 0);
lean_dec(v_unused_2319_);
v___x_2285_ = v_x_2262_;
v_isShared_2286_ = v_isSharedCheck_2318_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v_x_2262_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2318_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_node_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2317_; 
v_node_2287_ = lean_ctor_get(v_entry_2270_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_entry_2270_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2289_ = v_entry_2270_;
v_isShared_2290_ = v_isSharedCheck_2317_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_node_2287_);
lean_dec(v_entry_2270_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2317_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
size_t v___x_2291_; lean_object* v_entries_2292_; size_t v___x_2293_; lean_object* v_newNode_2294_; lean_object* v___x_2295_; 
v___x_2291_ = ((size_t)5ULL);
v_entries_2292_ = lean_array_set(v_es_2265_, v_j_2269_, v___x_2266_);
v___x_2293_ = lean_usize_shift_right(v_x_2263_, v___x_2291_);
v_newNode_2294_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2287_, v___x_2293_, v_x_2264_);
lean_inc_ref(v_newNode_2294_);
v___x_2295_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2294_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v___x_2297_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v_newNode_2294_);
v___x_2297_ = v___x_2289_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_newNode_2294_);
v___x_2297_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = lean_array_set(v_entries_2292_, v_j_2269_, v___x_2297_);
lean_dec(v_j_2269_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2298_);
v___x_2300_ = v___x_2285_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
else
{
lean_object* v_val_2303_; lean_object* v_fst_2304_; lean_object* v_snd_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v_newNode_2294_);
lean_del_object(v___x_2289_);
v_val_2303_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_val_2303_);
lean_dec_ref_known(v___x_2295_, 1);
v_fst_2304_ = lean_ctor_get(v_val_2303_, 0);
v_snd_2305_ = lean_ctor_get(v_val_2303_, 1);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_val_2303_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2307_ = v_val_2303_;
v_isShared_2308_ = v_isSharedCheck_2316_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_snd_2305_);
lean_inc(v_fst_2304_);
lean_dec(v_val_2303_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2316_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_fst_2304_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_snd_2305_);
v___x_2310_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = lean_array_set(v_entries_2292_, v_j_2269_, v___x_2310_);
lean_dec(v_j_2269_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2311_);
v___x_2313_ = v___x_2285_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2269_);
return v_x_2262_;
}
}
}
else
{
lean_object* v_ks_2320_; lean_object* v_vs_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2335_; 
v_ks_2320_ = lean_ctor_get(v_x_2262_, 0);
v_vs_2321_ = lean_ctor_get(v_x_2262_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_x_2262_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2323_ = v_x_2262_;
v_isShared_2324_ = v_isSharedCheck_2335_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_vs_2321_);
lean_inc(v_ks_2320_);
lean_dec(v_x_2262_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2335_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2320_, v_x_2264_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v___x_2327_; 
if (v_isShared_2324_ == 0)
{
v___x_2327_ = v___x_2323_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_ks_2320_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_vs_2321_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
else
{
lean_object* v_val_2329_; lean_object* v_keys_x27_2330_; lean_object* v_vals_x27_2331_; lean_object* v___x_2333_; 
v_val_2329_ = lean_ctor_get(v___x_2325_, 0);
lean_inc_n(v_val_2329_, 2);
lean_dec_ref_known(v___x_2325_, 1);
v_keys_x27_2330_ = l_Array_eraseIdx___redArg(v_ks_2320_, v_val_2329_);
v_vals_x27_2331_ = l_Array_eraseIdx___redArg(v_vs_2321_, v_val_2329_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 1, v_vals_x27_2331_);
lean_ctor_set(v___x_2323_, 0, v_keys_x27_2330_);
v___x_2333_ = v___x_2323_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_keys_x27_2330_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_vals_x27_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_){
_start:
{
size_t v_x_19389__boxed_2339_; lean_object* v_res_2340_; 
v_x_19389__boxed_2339_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_res_2340_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2336_, v_x_19389__boxed_2339_, v_x_2338_);
lean_dec_ref(v_x_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
size_t v___x_2343_; size_t v___x_2344_; size_t v___x_2345_; uint64_t v___x_2346_; size_t v_h_2347_; lean_object* v___x_2348_; 
v___x_2343_ = lean_ptr_addr(v_x_2342_);
v___x_2344_ = ((size_t)3ULL);
v___x_2345_ = lean_usize_shift_right(v___x_2343_, v___x_2344_);
v___x_2346_ = lean_usize_to_uint64(v___x_2345_);
v_h_2347_ = lean_uint64_to_usize(v___x_2346_);
v___x_2348_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2341_, v_h_2347_, v_x_2342_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2349_, v_x_2350_);
lean_dec_ref(v_x_2350_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
if (lean_obj_tag(v_as_2352_) == 0)
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_box(0);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
else
{
lean_object* v_head_2366_; lean_object* v_tail_2367_; lean_object* v___x_2368_; 
v_head_2366_ = lean_ctor_get(v_as_2352_, 0);
lean_inc(v_head_2366_);
v_tail_2367_ = lean_ctor_get(v_as_2352_, 1);
lean_inc(v_tail_2367_);
lean_dec_ref_known(v_as_2352_, 2);
v___x_2368_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2366_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_dec_ref_known(v___x_2368_, 1);
v_as_2352_ = v_tail_2367_;
goto _start;
}
else
{
lean_dec(v_tail_2367_);
return v___x_2368_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec(v___y_2371_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2383_, lean_object* v_vals_2384_, lean_object* v_i_2385_, lean_object* v_k_2386_){
_start:
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = lean_array_get_size(v_keys_2383_);
v___x_2388_ = lean_nat_dec_lt(v_i_2385_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; 
lean_dec(v_i_2385_);
v___x_2389_ = lean_box(0);
return v___x_2389_;
}
else
{
lean_object* v_k_x27_2390_; size_t v___x_2391_; size_t v___x_2392_; uint8_t v___x_2393_; 
v_k_x27_2390_ = lean_array_fget_borrowed(v_keys_2383_, v_i_2385_);
v___x_2391_ = lean_ptr_addr(v_k_2386_);
v___x_2392_ = lean_ptr_addr(v_k_x27_2390_);
v___x_2393_ = lean_usize_dec_eq(v___x_2391_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_unsigned_to_nat(1u);
v___x_2395_ = lean_nat_add(v_i_2385_, v___x_2394_);
lean_dec(v_i_2385_);
v_i_2385_ = v___x_2395_;
goto _start;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_array_fget_borrowed(v_vals_2384_, v_i_2385_);
lean_dec(v_i_2385_);
lean_inc(v___x_2397_);
v___x_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
return v___x_2398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2399_, lean_object* v_vals_2400_, lean_object* v_i_2401_, lean_object* v_k_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2399_, v_vals_2400_, v_i_2401_, v_k_2402_);
lean_dec_ref(v_k_2402_);
lean_dec_ref(v_vals_2400_);
lean_dec_ref(v_keys_2399_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2404_, size_t v_x_2405_, lean_object* v_x_2406_){
_start:
{
if (lean_obj_tag(v_x_2404_) == 0)
{
lean_object* v_es_2407_; lean_object* v___x_2408_; size_t v___x_2409_; size_t v___x_2410_; lean_object* v_j_2411_; lean_object* v___x_2412_; 
v_es_2407_ = lean_ctor_get(v_x_2404_, 0);
v___x_2408_ = lean_box(2);
v___x_2409_ = ((size_t)31ULL);
v___x_2410_ = lean_usize_land(v_x_2405_, v___x_2409_);
v_j_2411_ = lean_usize_to_nat(v___x_2410_);
v___x_2412_ = lean_array_get_borrowed(v___x_2408_, v_es_2407_, v_j_2411_);
lean_dec(v_j_2411_);
switch(lean_obj_tag(v___x_2412_))
{
case 0:
{
lean_object* v_key_2413_; lean_object* v_val_2414_; size_t v___x_2415_; size_t v___x_2416_; uint8_t v___x_2417_; 
v_key_2413_ = lean_ctor_get(v___x_2412_, 0);
v_val_2414_ = lean_ctor_get(v___x_2412_, 1);
v___x_2415_ = lean_ptr_addr(v_x_2406_);
v___x_2416_ = lean_ptr_addr(v_key_2413_);
v___x_2417_ = lean_usize_dec_eq(v___x_2415_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_box(0);
return v___x_2418_;
}
else
{
lean_object* v___x_2419_; 
lean_inc(v_val_2414_);
v___x_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2419_, 0, v_val_2414_);
return v___x_2419_;
}
}
case 1:
{
lean_object* v_node_2420_; size_t v___x_2421_; size_t v___x_2422_; 
v_node_2420_ = lean_ctor_get(v___x_2412_, 0);
v___x_2421_ = ((size_t)5ULL);
v___x_2422_ = lean_usize_shift_right(v_x_2405_, v___x_2421_);
v_x_2404_ = v_node_2420_;
v_x_2405_ = v___x_2422_;
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
v_ks_2425_ = lean_ctor_get(v_x_2404_, 0);
v_vs_2426_ = lean_ctor_get(v_x_2404_, 1);
v___x_2427_ = lean_unsigned_to_nat(0u);
v___x_2428_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2425_, v_vs_2426_, v___x_2427_, v_x_2406_);
return v___x_2428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2429_, lean_object* v_x_2430_, lean_object* v_x_2431_){
_start:
{
size_t v_x_19614__boxed_2432_; lean_object* v_res_2433_; 
v_x_19614__boxed_2432_ = lean_unbox_usize(v_x_2430_);
lean_dec(v_x_2430_);
v_res_2433_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2429_, v_x_19614__boxed_2432_, v_x_2431_);
lean_dec_ref(v_x_2431_);
lean_dec_ref(v_x_2429_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2434_, lean_object* v_x_2435_){
_start:
{
size_t v___x_2436_; size_t v___x_2437_; size_t v___x_2438_; uint64_t v___x_2439_; size_t v___x_2440_; lean_object* v___x_2441_; 
v___x_2436_ = lean_ptr_addr(v_x_2435_);
v___x_2437_ = ((size_t)3ULL);
v___x_2438_ = lean_usize_shift_right(v___x_2436_, v___x_2437_);
v___x_2439_ = lean_usize_to_uint64(v___x_2438_);
v___x_2440_ = lean_uint64_to_usize(v___x_2439_);
v___x_2441_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2434_, v___x_2440_, v_x_2435_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2442_, lean_object* v_x_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2442_, v_x_2443_);
lean_dec_ref(v_x_2443_);
lean_dec_ref(v_x_2442_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2445_, lean_object* v_b_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
if (lean_obj_tag(v_as_x27_2445_) == 0)
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v_b_2446_);
return v___x_2458_;
}
else
{
lean_object* v_head_2459_; lean_object* v_tail_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v_toGoalState_2463_; lean_object* v_ematch_2464_; lean_object* v_delayedThmInsts_2465_; lean_object* v___x_2466_; 
v_head_2459_ = lean_ctor_get(v_as_x27_2445_, 0);
v_tail_2460_ = lean_ctor_get(v_as_x27_2445_, 1);
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_st_ref_get(v___y_2447_);
v_toGoalState_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc_ref(v_toGoalState_2463_);
lean_dec(v___x_2462_);
v_ematch_2464_ = lean_ctor_get(v_toGoalState_2463_, 12);
lean_inc_ref(v_ematch_2464_);
lean_dec_ref(v_toGoalState_2463_);
v_delayedThmInsts_2465_ = lean_ctor_get(v_ematch_2464_, 10);
lean_inc_ref(v_delayedThmInsts_2465_);
lean_dec_ref(v_ematch_2464_);
v___x_2466_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2465_, v_head_2459_);
lean_dec_ref(v_delayedThmInsts_2465_);
if (lean_obj_tag(v___x_2466_) == 1)
{
lean_object* v_val_2467_; lean_object* v___x_2468_; lean_object* v_toGoalState_2469_; lean_object* v_ematch_2470_; lean_object* v_mvarId_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2525_; 
v_val_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_val_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2468_ = lean_st_ref_take(v___y_2447_);
v_toGoalState_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_ref(v_toGoalState_2469_);
v_ematch_2470_ = lean_ctor_get(v_toGoalState_2469_, 12);
lean_inc_ref(v_ematch_2470_);
v_mvarId_2471_ = lean_ctor_get(v___x_2468_, 1);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; 
v_unused_2526_ = lean_ctor_get(v___x_2468_, 0);
lean_dec(v_unused_2526_);
v___x_2473_ = v___x_2468_;
v_isShared_2474_ = v_isSharedCheck_2525_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_mvarId_2471_);
lean_dec(v___x_2468_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2525_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v_nextDeclIdx_2475_; lean_object* v_enodeMap_2476_; lean_object* v_exprs_2477_; lean_object* v_parents_2478_; lean_object* v_congrTable_2479_; lean_object* v_appMap_2480_; lean_object* v_indicesFound_2481_; lean_object* v_newFacts_2482_; uint8_t v_inconsistent_2483_; lean_object* v_nextIdx_2484_; lean_object* v_newRawFacts_2485_; lean_object* v_facts_2486_; lean_object* v_extThms_2487_; lean_object* v_inj_2488_; lean_object* v_split_2489_; lean_object* v_clean_2490_; lean_object* v_sstates_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2523_; 
v_nextDeclIdx_2475_ = lean_ctor_get(v_toGoalState_2469_, 0);
v_enodeMap_2476_ = lean_ctor_get(v_toGoalState_2469_, 1);
v_exprs_2477_ = lean_ctor_get(v_toGoalState_2469_, 2);
v_parents_2478_ = lean_ctor_get(v_toGoalState_2469_, 3);
v_congrTable_2479_ = lean_ctor_get(v_toGoalState_2469_, 4);
v_appMap_2480_ = lean_ctor_get(v_toGoalState_2469_, 5);
v_indicesFound_2481_ = lean_ctor_get(v_toGoalState_2469_, 6);
v_newFacts_2482_ = lean_ctor_get(v_toGoalState_2469_, 7);
v_inconsistent_2483_ = lean_ctor_get_uint8(v_toGoalState_2469_, sizeof(void*)*17);
v_nextIdx_2484_ = lean_ctor_get(v_toGoalState_2469_, 8);
v_newRawFacts_2485_ = lean_ctor_get(v_toGoalState_2469_, 9);
v_facts_2486_ = lean_ctor_get(v_toGoalState_2469_, 10);
v_extThms_2487_ = lean_ctor_get(v_toGoalState_2469_, 11);
v_inj_2488_ = lean_ctor_get(v_toGoalState_2469_, 13);
v_split_2489_ = lean_ctor_get(v_toGoalState_2469_, 14);
v_clean_2490_ = lean_ctor_get(v_toGoalState_2469_, 15);
v_sstates_2491_ = lean_ctor_get(v_toGoalState_2469_, 16);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_toGoalState_2469_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v_toGoalState_2469_, 12);
lean_dec(v_unused_2524_);
v___x_2493_ = v_toGoalState_2469_;
v_isShared_2494_ = v_isSharedCheck_2523_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_sstates_2491_);
lean_inc(v_clean_2490_);
lean_inc(v_split_2489_);
lean_inc(v_inj_2488_);
lean_inc(v_extThms_2487_);
lean_inc(v_facts_2486_);
lean_inc(v_newRawFacts_2485_);
lean_inc(v_nextIdx_2484_);
lean_inc(v_newFacts_2482_);
lean_inc(v_indicesFound_2481_);
lean_inc(v_appMap_2480_);
lean_inc(v_congrTable_2479_);
lean_inc(v_parents_2478_);
lean_inc(v_exprs_2477_);
lean_inc(v_enodeMap_2476_);
lean_inc(v_nextDeclIdx_2475_);
lean_dec(v_toGoalState_2469_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2523_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v_thmMap_2495_; lean_object* v_gmt_2496_; lean_object* v_thms_2497_; lean_object* v_newThms_2498_; lean_object* v_numInstances_2499_; lean_object* v_numDelayedInstances_2500_; lean_object* v_num_2501_; lean_object* v_preInstances_2502_; lean_object* v_nextThmIdx_2503_; lean_object* v_matchEqNames_2504_; lean_object* v_delayedThmInsts_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2522_; 
v_thmMap_2495_ = lean_ctor_get(v_ematch_2470_, 0);
v_gmt_2496_ = lean_ctor_get(v_ematch_2470_, 1);
v_thms_2497_ = lean_ctor_get(v_ematch_2470_, 2);
v_newThms_2498_ = lean_ctor_get(v_ematch_2470_, 3);
v_numInstances_2499_ = lean_ctor_get(v_ematch_2470_, 4);
v_numDelayedInstances_2500_ = lean_ctor_get(v_ematch_2470_, 5);
v_num_2501_ = lean_ctor_get(v_ematch_2470_, 6);
v_preInstances_2502_ = lean_ctor_get(v_ematch_2470_, 7);
v_nextThmIdx_2503_ = lean_ctor_get(v_ematch_2470_, 8);
v_matchEqNames_2504_ = lean_ctor_get(v_ematch_2470_, 9);
v_delayedThmInsts_2505_ = lean_ctor_get(v_ematch_2470_, 10);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_ematch_2470_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2507_ = v_ematch_2470_;
v_isShared_2508_ = v_isSharedCheck_2522_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_delayedThmInsts_2505_);
lean_inc(v_matchEqNames_2504_);
lean_inc(v_nextThmIdx_2503_);
lean_inc(v_preInstances_2502_);
lean_inc(v_num_2501_);
lean_inc(v_numDelayedInstances_2500_);
lean_inc(v_numInstances_2499_);
lean_inc(v_newThms_2498_);
lean_inc(v_thms_2497_);
lean_inc(v_gmt_2496_);
lean_inc(v_thmMap_2495_);
lean_dec(v_ematch_2470_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2522_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2505_, v_head_2459_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 10, v___x_2509_);
v___x_2511_ = v___x_2507_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_thmMap_2495_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_gmt_2496_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_thms_2497_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v_newThms_2498_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v_numInstances_2499_);
lean_ctor_set(v_reuseFailAlloc_2521_, 5, v_numDelayedInstances_2500_);
lean_ctor_set(v_reuseFailAlloc_2521_, 6, v_num_2501_);
lean_ctor_set(v_reuseFailAlloc_2521_, 7, v_preInstances_2502_);
lean_ctor_set(v_reuseFailAlloc_2521_, 8, v_nextThmIdx_2503_);
lean_ctor_set(v_reuseFailAlloc_2521_, 9, v_matchEqNames_2504_);
lean_ctor_set(v_reuseFailAlloc_2521_, 10, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2513_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 12, v___x_2511_);
v___x_2513_ = v___x_2493_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_nextDeclIdx_2475_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_enodeMap_2476_);
lean_ctor_set(v_reuseFailAlloc_2520_, 2, v_exprs_2477_);
lean_ctor_set(v_reuseFailAlloc_2520_, 3, v_parents_2478_);
lean_ctor_set(v_reuseFailAlloc_2520_, 4, v_congrTable_2479_);
lean_ctor_set(v_reuseFailAlloc_2520_, 5, v_appMap_2480_);
lean_ctor_set(v_reuseFailAlloc_2520_, 6, v_indicesFound_2481_);
lean_ctor_set(v_reuseFailAlloc_2520_, 7, v_newFacts_2482_);
lean_ctor_set(v_reuseFailAlloc_2520_, 8, v_nextIdx_2484_);
lean_ctor_set(v_reuseFailAlloc_2520_, 9, v_newRawFacts_2485_);
lean_ctor_set(v_reuseFailAlloc_2520_, 10, v_facts_2486_);
lean_ctor_set(v_reuseFailAlloc_2520_, 11, v_extThms_2487_);
lean_ctor_set(v_reuseFailAlloc_2520_, 12, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2520_, 13, v_inj_2488_);
lean_ctor_set(v_reuseFailAlloc_2520_, 14, v_split_2489_);
lean_ctor_set(v_reuseFailAlloc_2520_, 15, v_clean_2490_);
lean_ctor_set(v_reuseFailAlloc_2520_, 16, v_sstates_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2520_, sizeof(void*)*17, v_inconsistent_2483_);
v___x_2513_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2515_; 
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2513_);
v___x_2515_ = v___x_2473_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_mvarId_2471_);
v___x_2515_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_st_ref_put(v___y_2447_, v___x_2515_);
v___x_2517_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2467_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_dec_ref_known(v___x_2517_, 1);
v_as_x27_2445_ = v_tail_2460_;
v_b_2446_ = v___x_2461_;
goto _start;
}
else
{
return v___x_2517_;
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
lean_dec(v___x_2466_);
v_as_x27_2445_ = v_tail_2460_;
v_b_2446_ = v___x_2461_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2528_, lean_object* v_b_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2528_, v_b_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec(v_as_x27_2528_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2543_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2583_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2583_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2583_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
uint8_t v___x_2559_; 
v___x_2559_ = lean_unbox(v_a_2555_);
lean_dec(v_a_2555_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v_toGoalState_2561_; lean_object* v_ematch_2562_; lean_object* v_delayedThmInsts_2563_; uint8_t v___x_2564_; 
v___x_2560_ = lean_st_ref_get(v_a_2543_);
v_toGoalState_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc_ref(v_toGoalState_2561_);
lean_dec(v___x_2560_);
v_ematch_2562_ = lean_ctor_get(v_toGoalState_2561_, 12);
lean_inc_ref(v_ematch_2562_);
lean_dec_ref(v_toGoalState_2561_);
v_delayedThmInsts_2563_ = lean_ctor_get(v_ematch_2562_, 10);
lean_inc_ref(v_delayedThmInsts_2563_);
lean_dec_ref(v_ematch_2562_);
v___x_2564_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2563_);
lean_dec_ref(v_delayedThmInsts_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
lean_del_object(v___x_2557_);
v___x_2565_ = lean_box(0);
v___x_2566_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2542_, v___x_2565_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; 
v_unused_2574_ = lean_ctor_get(v___x_2566_, 0);
lean_dec(v_unused_2574_);
v___x_2568_ = v___x_2566_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_dec(v___x_2566_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2565_);
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2565_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
else
{
return v___x_2566_;
}
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_box(0);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2575_);
v___x_2577_ = v___x_2557_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2579_ = lean_box(0);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2579_);
v___x_2581_ = v___x_2557_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
v_a_2584_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2554_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2554_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
lean_dec(v_a_2602_);
lean_dec_ref(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec(v_toPropagateDown_2592_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2605_, lean_object* v_x_2606_, lean_object* v_x_2607_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2606_, v_x_2607_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2609_, lean_object* v_x_2610_, lean_object* v_x_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2609_, v_x_2610_, v_x_2611_);
lean_dec_ref(v_x_2611_);
lean_dec_ref(v_x_2610_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2613_, lean_object* v_x_2614_, lean_object* v_x_2615_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2614_, v_x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2617_, v_x_2618_, v_x_2619_);
lean_dec_ref(v_x_2619_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2621_, lean_object* v_as_x27_2622_, lean_object* v_b_2623_, lean_object* v_a_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2622_, v_b_2623_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2637_, lean_object* v_as_x27_2638_, lean_object* v_b_2639_, lean_object* v_a_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2637_, v_as_x27_2638_, v_b_2639_, v_a_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec(v_as_x27_2638_);
lean_dec(v_as_2637_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2653_, lean_object* v_x_2654_, size_t v_x_2655_, lean_object* v_x_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2654_, v_x_2655_, v_x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2658_, lean_object* v_x_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_){
_start:
{
size_t v_x_19919__boxed_2662_; lean_object* v_res_2663_; 
v_x_19919__boxed_2662_ = lean_unbox_usize(v_x_2660_);
lean_dec(v_x_2660_);
v_res_2663_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2658_, v_x_2659_, v_x_19919__boxed_2662_, v_x_2661_);
lean_dec_ref(v_x_2661_);
lean_dec_ref(v_x_2659_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2664_, lean_object* v_x_2665_, size_t v_x_2666_, lean_object* v_x_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2665_, v_x_2666_, v_x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2669_, lean_object* v_x_2670_, lean_object* v_x_2671_, lean_object* v_x_2672_){
_start:
{
size_t v_x_19930__boxed_2673_; lean_object* v_res_2674_; 
v_x_19930__boxed_2673_ = lean_unbox_usize(v_x_2671_);
lean_dec(v_x_2671_);
v_res_2674_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2669_, v_x_2670_, v_x_19930__boxed_2673_, v_x_2672_);
lean_dec_ref(v_x_2672_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2675_, lean_object* v_keys_2676_, lean_object* v_vals_2677_, lean_object* v_heq_2678_, lean_object* v_i_2679_, lean_object* v_k_2680_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2676_, v_vals_2677_, v_i_2679_, v_k_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2682_, lean_object* v_keys_2683_, lean_object* v_vals_2684_, lean_object* v_heq_2685_, lean_object* v_i_2686_, lean_object* v_k_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2682_, v_keys_2683_, v_vals_2684_, v_heq_2685_, v_i_2686_, v_k_2687_);
lean_dec_ref(v_k_2687_);
lean_dec_ref(v_vals_2684_);
lean_dec_ref(v_keys_2683_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2689_, lean_object* v_keys_2690_, lean_object* v_vals_2691_, lean_object* v_i_2692_, lean_object* v_k_2693_){
_start:
{
lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2694_ = lean_array_get_size(v_keys_2690_);
v___x_2695_ = lean_nat_dec_lt(v_i_2692_, v___x_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; 
lean_dec_ref(v_k_2693_);
lean_dec(v_i_2692_);
v___x_2696_ = lean_box(0);
return v___x_2696_;
}
else
{
lean_object* v_k_x27_2697_; uint8_t v___x_2698_; 
v_k_x27_2697_ = lean_array_fget_borrowed(v_keys_2690_, v_i_2692_);
lean_inc(v_k_x27_2697_);
lean_inc_ref(v_k_2693_);
v___x_2698_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2689_, v_k_2693_, v_k_x27_2697_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = lean_unsigned_to_nat(1u);
v___x_2700_ = lean_nat_add(v_i_2692_, v___x_2699_);
lean_dec(v_i_2692_);
v_i_2692_ = v___x_2700_;
goto _start;
}
else
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_dec_ref(v_k_2693_);
v___x_2702_ = lean_array_fget_borrowed(v_vals_2691_, v_i_2692_);
lean_dec(v_i_2692_);
lean_inc(v___x_2702_);
lean_inc(v_k_x27_2697_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_k_x27_2697_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2705_, lean_object* v_keys_2706_, lean_object* v_vals_2707_, lean_object* v_i_2708_, lean_object* v_k_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2705_, v_keys_2706_, v_vals_2707_, v_i_2708_, v_k_2709_);
lean_dec_ref(v_vals_2707_);
lean_dec_ref(v_keys_2706_);
lean_dec_ref(v___x_2705_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2711_, lean_object* v_x_2712_, size_t v_x_2713_, lean_object* v_x_2714_){
_start:
{
if (lean_obj_tag(v_x_2712_) == 0)
{
lean_object* v_es_2715_; lean_object* v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; lean_object* v_j_2719_; lean_object* v___x_2720_; 
v_es_2715_ = lean_ctor_get(v_x_2712_, 0);
lean_inc_ref(v_es_2715_);
lean_dec_ref_known(v_x_2712_, 1);
v___x_2716_ = lean_box(2);
v___x_2717_ = ((size_t)31ULL);
v___x_2718_ = lean_usize_land(v_x_2713_, v___x_2717_);
v_j_2719_ = lean_usize_to_nat(v___x_2718_);
v___x_2720_ = lean_array_get(v___x_2716_, v_es_2715_, v_j_2719_);
lean_dec(v_j_2719_);
lean_dec_ref(v_es_2715_);
switch(lean_obj_tag(v___x_2720_))
{
case 0:
{
lean_object* v_key_2721_; lean_object* v_val_2722_; uint8_t v___x_2723_; 
v_key_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc_n(v_key_2721_, 2);
v_val_2722_ = lean_ctor_get(v___x_2720_, 1);
lean_inc(v_val_2722_);
lean_dec_ref_known(v___x_2720_, 2);
v___x_2723_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2711_, v_x_2714_, v_key_2721_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; 
lean_dec(v_val_2722_);
lean_dec(v_key_2721_);
v___x_2724_ = lean_box(0);
return v___x_2724_;
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v_key_2721_);
lean_ctor_set(v___x_2725_, 1, v_val_2722_);
v___x_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
}
case 1:
{
lean_object* v_node_2727_; size_t v___x_2728_; size_t v___x_2729_; 
v_node_2727_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_node_2727_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2728_ = ((size_t)5ULL);
v___x_2729_ = lean_usize_shift_right(v_x_2713_, v___x_2728_);
v_x_2712_ = v_node_2727_;
v_x_2713_ = v___x_2729_;
goto _start;
}
default: 
{
lean_object* v___x_2731_; 
lean_dec_ref(v_x_2714_);
v___x_2731_ = lean_box(0);
return v___x_2731_;
}
}
}
else
{
lean_object* v_ks_2732_; lean_object* v_vs_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_ks_2732_ = lean_ctor_get(v_x_2712_, 0);
lean_inc_ref(v_ks_2732_);
v_vs_2733_ = lean_ctor_get(v_x_2712_, 1);
lean_inc_ref(v_vs_2733_);
lean_dec_ref_known(v_x_2712_, 2);
v___x_2734_ = lean_unsigned_to_nat(0u);
v___x_2735_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2711_, v_ks_2732_, v_vs_2733_, v___x_2734_, v_x_2714_);
lean_dec_ref(v_vs_2733_);
lean_dec_ref(v_ks_2732_);
return v___x_2735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_, lean_object* v_x_2739_){
_start:
{
size_t v_x_25951__boxed_2740_; lean_object* v_res_2741_; 
v_x_25951__boxed_2740_ = lean_unbox_usize(v_x_2738_);
lean_dec(v_x_2738_);
v_res_2741_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2736_, v_x_2737_, v_x_25951__boxed_2740_, v_x_2739_);
lean_dec_ref(v___x_2736_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2742_, lean_object* v_x_2743_, lean_object* v_x_2744_){
_start:
{
uint64_t v___x_2745_; size_t v___x_2746_; lean_object* v___x_2747_; 
lean_inc_ref(v_x_2744_);
v___x_2745_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2742_, v_x_2744_);
v___x_2746_ = lean_uint64_to_usize(v___x_2745_);
lean_inc_ref(v_x_2743_);
v___x_2747_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2742_, v_x_2743_, v___x_2746_, v_x_2744_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2748_, lean_object* v_x_2749_, lean_object* v_x_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2748_, v_x_2749_, v_x_2750_);
lean_dec_ref(v_x_2749_);
lean_dec_ref(v___x_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_){
_start:
{
lean_object* v_ks_2757_; lean_object* v_vs_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2782_; 
v_ks_2757_ = lean_ctor_get(v_x_2753_, 0);
v_vs_2758_ = lean_ctor_get(v_x_2753_, 1);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_x_2753_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2760_ = v_x_2753_;
v_isShared_2761_ = v_isSharedCheck_2782_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_vs_2758_);
lean_inc(v_ks_2757_);
lean_dec(v_x_2753_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2782_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2762_ = lean_array_get_size(v_ks_2757_);
v___x_2763_ = lean_nat_dec_lt(v_x_2754_, v___x_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
lean_dec(v_x_2754_);
v___x_2764_ = lean_array_push(v_ks_2757_, v_x_2755_);
v___x_2765_ = lean_array_push(v_vs_2758_, v_x_2756_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 1, v___x_2765_);
lean_ctor_set(v___x_2760_, 0, v___x_2764_);
v___x_2767_ = v___x_2760_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
else
{
lean_object* v_k_x27_2769_; uint8_t v___x_2770_; 
v_k_x27_2769_ = lean_array_fget_borrowed(v_ks_2757_, v_x_2754_);
lean_inc(v_k_x27_2769_);
lean_inc_ref(v_x_2755_);
v___x_2770_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2752_, v_x_2755_, v_k_x27_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2772_; 
if (v_isShared_2761_ == 0)
{
v___x_2772_ = v___x_2760_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_ks_2757_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_vs_2758_);
v___x_2772_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = lean_unsigned_to_nat(1u);
v___x_2774_ = lean_nat_add(v_x_2754_, v___x_2773_);
lean_dec(v_x_2754_);
v_x_2753_ = v___x_2772_;
v_x_2754_ = v___x_2774_;
goto _start;
}
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2777_ = lean_array_fset(v_ks_2757_, v_x_2754_, v_x_2755_);
v___x_2778_ = lean_array_fset(v_vs_2758_, v_x_2754_, v_x_2756_);
lean_dec(v_x_2754_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 1, v___x_2778_);
lean_ctor_set(v___x_2760_, 0, v___x_2777_);
v___x_2780_ = v___x_2760_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2777_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2783_, lean_object* v_x_2784_, lean_object* v_x_2785_, lean_object* v_x_2786_, lean_object* v_x_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2783_, v_x_2784_, v_x_2785_, v_x_2786_, v_x_2787_);
lean_dec_ref(v___x_2783_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2789_, lean_object* v_n_2790_, lean_object* v_k_2791_, lean_object* v_v_2792_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2789_, v_n_2790_, v___x_2793_, v_k_2791_, v_v_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2795_, lean_object* v_n_2796_, lean_object* v_k_2797_, lean_object* v_v_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2795_, v_n_2796_, v_k_2797_, v_v_2798_);
lean_dec_ref(v___x_2795_);
return v_res_2799_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2801_, lean_object* v_x_2802_, size_t v_x_2803_, size_t v_x_2804_, lean_object* v_x_2805_, lean_object* v_x_2806_){
_start:
{
if (lean_obj_tag(v_x_2802_) == 0)
{
lean_object* v_es_2807_; size_t v___x_2808_; size_t v___x_2809_; lean_object* v_j_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v_es_2807_ = lean_ctor_get(v_x_2802_, 0);
v___x_2808_ = ((size_t)31ULL);
v___x_2809_ = lean_usize_land(v_x_2803_, v___x_2808_);
v_j_2810_ = lean_usize_to_nat(v___x_2809_);
v___x_2811_ = lean_array_get_size(v_es_2807_);
v___x_2812_ = lean_nat_dec_lt(v_j_2810_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_dec(v_j_2810_);
lean_dec(v_x_2806_);
lean_dec_ref(v_x_2805_);
return v_x_2802_;
}
else
{
lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2851_; 
lean_inc_ref(v_es_2807_);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_x_2802_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; 
v_unused_2852_ = lean_ctor_get(v_x_2802_, 0);
lean_dec(v_unused_2852_);
v___x_2814_ = v_x_2802_;
v_isShared_2815_ = v_isSharedCheck_2851_;
goto v_resetjp_2813_;
}
else
{
lean_dec(v_x_2802_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2851_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_v_2816_; lean_object* v___x_2817_; lean_object* v_xs_x27_2818_; lean_object* v___y_2820_; 
v_v_2816_ = lean_array_fget(v_es_2807_, v_j_2810_);
v___x_2817_ = lean_box(0);
v_xs_x27_2818_ = lean_array_fset(v_es_2807_, v_j_2810_, v___x_2817_);
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
lean_inc_ref(v_x_2805_);
v___x_2830_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2801_, v_x_2805_, v_key_2825_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_del_object(v___x_2828_);
v___x_2831_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2825_, v_val_2826_, v_x_2805_, v_x_2806_);
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
lean_ctor_set(v___x_2828_, 1, v_x_2806_);
lean_ctor_set(v___x_2828_, 0, v_x_2805_);
v___x_2834_ = v___x_2828_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_x_2805_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_x_2806_);
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
lean_object* v_node_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2849_; 
v_node_2837_ = lean_ctor_get(v_v_2816_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_v_2816_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2839_ = v_v_2816_;
v_isShared_2840_ = v_isSharedCheck_2849_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_node_2837_);
lean_dec(v_v_2816_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2849_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
size_t v___x_2841_; size_t v___x_2842_; size_t v___x_2843_; size_t v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2841_ = ((size_t)5ULL);
v___x_2842_ = lean_usize_shift_right(v_x_2803_, v___x_2841_);
v___x_2843_ = ((size_t)1ULL);
v___x_2844_ = lean_usize_add(v_x_2804_, v___x_2843_);
v___x_2845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2801_, v_node_2837_, v___x_2842_, v___x_2844_, v_x_2805_, v_x_2806_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2845_);
v___x_2847_ = v___x_2839_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
v___y_2820_ = v___x_2847_;
goto v___jp_2819_;
}
}
}
default: 
{
lean_object* v___x_2850_; 
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_x_2805_);
lean_ctor_set(v___x_2850_, 1, v_x_2806_);
v___y_2820_ = v___x_2850_;
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
lean_object* v_ks_2853_; lean_object* v_vs_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2872_; 
v_ks_2853_ = lean_ctor_get(v_x_2802_, 0);
v_vs_2854_ = lean_ctor_get(v_x_2802_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_x_2802_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2856_ = v_x_2802_;
v_isShared_2857_ = v_isSharedCheck_2872_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_vs_2854_);
lean_inc(v_ks_2853_);
lean_dec(v_x_2802_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2872_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_ks_2853_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_vs_2854_);
v___x_2859_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v_newNode_2860_; size_t v___x_2861_; uint8_t v___x_2862_; 
v_newNode_2860_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2801_, v___x_2859_, v_x_2805_, v_x_2806_);
v___x_2861_ = ((size_t)7ULL);
v___x_2862_ = lean_usize_dec_le(v___x_2861_, v_x_2804_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2860_);
v___x_2864_ = lean_unsigned_to_nat(4u);
v___x_2865_ = lean_nat_dec_lt(v___x_2863_, v___x_2864_);
lean_dec(v___x_2863_);
if (v___x_2865_ == 0)
{
lean_object* v_ks_2866_; lean_object* v_vs_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_ks_2866_ = lean_ctor_get(v_newNode_2860_, 0);
lean_inc_ref(v_ks_2866_);
v_vs_2867_ = lean_ctor_get(v_newNode_2860_, 1);
lean_inc_ref(v_vs_2867_);
lean_dec_ref(v_newNode_2860_);
v___x_2868_ = lean_unsigned_to_nat(0u);
v___x_2869_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2870_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2801_, v_x_2804_, v_ks_2866_, v_vs_2867_, v___x_2868_, v___x_2869_);
lean_dec_ref(v_vs_2867_);
lean_dec_ref(v_ks_2866_);
return v___x_2870_;
}
else
{
return v_newNode_2860_;
}
}
else
{
return v_newNode_2860_;
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
size_t v_x_26105__boxed_2908_; size_t v_x_26106__boxed_2909_; lean_object* v_res_2910_; 
v_x_26105__boxed_2908_ = lean_unbox_usize(v_x_2904_);
lean_dec(v_x_2904_);
v_x_26106__boxed_2909_ = lean_unbox_usize(v_x_2905_);
lean_dec(v_x_2905_);
v_res_2910_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2902_, v_x_2903_, v_x_26105__boxed_2908_, v_x_26106__boxed_2909_, v_x_2906_, v_x_2907_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2928_, lean_object* v_rootNew_2929_, uint8_t v_a_2930_, lean_object* v_a_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_snd_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_3109_; 
v_snd_2939_ = lean_ctor_get(v_a_2931_, 1);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_a_2931_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; 
v_unused_3110_ = lean_ctor_get(v_a_2931_, 0);
lean_dec(v_unused_3110_);
v___x_2941_ = v_a_2931_;
v_isShared_2942_ = v_isSharedCheck_3109_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_snd_2939_);
lean_dec(v_a_2931_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_3109_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2943_ = lean_box(0);
v___x_2944_ = lean_st_ref_get(v___y_2932_);
lean_inc(v_snd_2939_);
v___x_2945_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2944_, v_snd_2939_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___x_2944_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_3100_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_3100_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_3100_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v_self_2950_; lean_object* v_next_2951_; lean_object* v_congr_2952_; lean_object* v_target_x3f_2953_; lean_object* v_proof_x3f_2954_; uint8_t v_flipped_2955_; lean_object* v_size_2956_; uint8_t v_interpreted_2957_; uint8_t v_ctor_2958_; uint8_t v_hasLambdas_2959_; uint8_t v_heqProofs_2960_; lean_object* v_idx_2961_; lean_object* v_generation_2962_; lean_object* v_mt_2963_; lean_object* v_sTerms_2964_; uint8_t v_funCC_2965_; lean_object* v_ematchDiagSource_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3098_; 
v_self_2950_ = lean_ctor_get(v_a_2946_, 0);
v_next_2951_ = lean_ctor_get(v_a_2946_, 1);
v_congr_2952_ = lean_ctor_get(v_a_2946_, 3);
v_target_x3f_2953_ = lean_ctor_get(v_a_2946_, 4);
v_proof_x3f_2954_ = lean_ctor_get(v_a_2946_, 5);
v_flipped_2955_ = lean_ctor_get_uint8(v_a_2946_, sizeof(void*)*12);
v_size_2956_ = lean_ctor_get(v_a_2946_, 6);
v_interpreted_2957_ = lean_ctor_get_uint8(v_a_2946_, sizeof(void*)*12 + 1);
v_ctor_2958_ = lean_ctor_get_uint8(v_a_2946_, sizeof(void*)*12 + 2);
v_hasLambdas_2959_ = lean_ctor_get_uint8(v_a_2946_, sizeof(void*)*12 + 3);
v_heqProofs_2960_ = lean_ctor_get_uint8(v_a_2946_, sizeof(void*)*12 + 4);
v_idx_2961_ = lean_ctor_get(v_a_2946_, 7);
v_generation_2962_ = lean_ctor_get(v_a_2946_, 8);
v_mt_2963_ = lean_ctor_get(v_a_2946_, 9);
v_sTerms_2964_ = lean_ctor_get(v_a_2946_, 10);
v_funCC_2965_ = lean_ctor_get_uint8(v_a_2946_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2966_ = lean_ctor_get(v_a_2946_, 11);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_a_2946_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; 
v_unused_3099_ = lean_ctor_get(v_a_2946_, 2);
lean_dec(v_unused_3099_);
v___x_2968_ = v_a_2946_;
v_isShared_2969_ = v_isSharedCheck_3098_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_ematchDiagSource_2966_);
lean_inc(v_sTerms_2964_);
lean_inc(v_mt_2963_);
lean_inc(v_generation_2962_);
lean_inc(v_idx_2961_);
lean_inc(v_size_2956_);
lean_inc(v_proof_x3f_2954_);
lean_inc(v_target_x3f_2953_);
lean_inc(v_congr_2952_);
lean_inc(v_next_2951_);
lean_inc(v_self_2950_);
lean_dec(v_a_2946_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3098_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___y_2986_; lean_object* v___x_2996_; 
lean_inc(v_ematchDiagSource_2966_);
lean_inc(v_sTerms_2964_);
lean_inc(v_mt_2963_);
lean_inc(v_generation_2962_);
lean_inc(v_idx_2961_);
lean_inc(v_size_2956_);
lean_inc(v_proof_x3f_2954_);
lean_inc(v_target_x3f_2953_);
lean_inc_ref(v_rootNew_2929_);
lean_inc_ref(v_next_2951_);
lean_inc_ref(v_self_2950_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 2, v_rootNew_2929_);
v___x_2996_ = v___x_2968_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_self_2950_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_next_2951_);
lean_ctor_set(v_reuseFailAlloc_3097_, 2, v_rootNew_2929_);
lean_ctor_set(v_reuseFailAlloc_3097_, 3, v_congr_2952_);
lean_ctor_set(v_reuseFailAlloc_3097_, 4, v_target_x3f_2953_);
lean_ctor_set(v_reuseFailAlloc_3097_, 5, v_proof_x3f_2954_);
lean_ctor_set(v_reuseFailAlloc_3097_, 6, v_size_2956_);
lean_ctor_set(v_reuseFailAlloc_3097_, 7, v_idx_2961_);
lean_ctor_set(v_reuseFailAlloc_3097_, 8, v_generation_2962_);
lean_ctor_set(v_reuseFailAlloc_3097_, 9, v_mt_2963_);
lean_ctor_set(v_reuseFailAlloc_3097_, 10, v_sTerms_2964_);
lean_ctor_set(v_reuseFailAlloc_3097_, 11, v_ematchDiagSource_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_3097_, sizeof(void*)*12, v_flipped_2955_);
lean_ctor_set_uint8(v_reuseFailAlloc_3097_, sizeof(void*)*12 + 1, v_interpreted_2957_);
lean_ctor_set_uint8(v_reuseFailAlloc_3097_, sizeof(void*)*12 + 2, v_ctor_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3097_, sizeof(void*)*12 + 3, v_hasLambdas_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_3097_, sizeof(void*)*12 + 4, v_heqProofs_2960_);
lean_ctor_set_uint8(v_reuseFailAlloc_3097_, sizeof(void*)*12 + 5, v_funCC_2965_);
v___x_2996_ = v_reuseFailAlloc_3097_;
goto v_reusejp_2995_;
}
v___jp_2970_:
{
size_t v___x_2971_; size_t v___x_2972_; uint8_t v___x_2973_; 
v___x_2971_ = lean_ptr_addr(v_next_2951_);
v___x_2972_ = lean_ptr_addr(v_lhs_2928_);
v___x_2973_ = lean_usize_dec_eq(v___x_2971_, v___x_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2975_; 
lean_del_object(v___x_2948_);
lean_dec(v_snd_2939_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v_next_2951_);
lean_ctor_set(v___x_2941_, 0, v___x_2943_);
v___x_2975_ = v___x_2941_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_next_2951_);
v___x_2975_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
v_a_2931_ = v___x_2975_;
goto _start;
}
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
lean_dec_ref(v_next_2951_);
lean_dec_ref(v_rootNew_2929_);
v___x_2978_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v___x_2978_);
v___x_2980_ = v___x_2941_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_snd_2939_);
v___x_2980_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2982_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2980_);
v___x_2982_ = v___x_2948_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
v___jp_2985_:
{
if (lean_obj_tag(v___y_2986_) == 0)
{
lean_dec_ref_known(v___y_2986_, 1);
goto v___jp_2970_;
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec_ref(v_next_2951_);
lean_del_object(v___x_2948_);
lean_del_object(v___x_2941_);
lean_dec(v_snd_2939_);
lean_dec_ref(v_rootNew_2929_);
v_a_2987_ = lean_ctor_get(v___y_2986_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___y_2986_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___y_2986_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___y_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; 
lean_inc_ref(v___x_2996_);
lean_inc_ref(v_self_2950_);
v___x_2997_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2950_, v___x_2996_, v___y_2932_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_dec_ref_known(v___x_2997_, 1);
if (v_a_2930_ == 0)
{
lean_dec_ref(v___x_2996_);
lean_dec(v_ematchDiagSource_2966_);
lean_dec(v_sTerms_2964_);
lean_dec(v_mt_2963_);
lean_dec(v_generation_2962_);
lean_dec(v_idx_2961_);
lean_dec(v_size_2956_);
lean_dec(v_proof_x3f_2954_);
lean_dec(v_target_x3f_2953_);
lean_dec_ref(v_self_2950_);
goto v___jp_2970_;
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2998_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_2999_ = lean_unsigned_to_nat(3u);
v___x_3000_ = l_Lean_Expr_isAppOfArity(v_self_2950_, v___x_2998_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_dec_ref(v___x_2996_);
lean_dec(v_ematchDiagSource_2966_);
lean_dec(v_sTerms_2964_);
lean_dec(v_mt_2963_);
lean_dec(v_generation_2962_);
lean_dec(v_idx_2961_);
lean_dec(v_size_2956_);
lean_dec(v_proof_x3f_2954_);
lean_dec(v_target_x3f_2953_);
lean_dec_ref(v_self_2950_);
goto v___jp_2970_;
}
else
{
uint8_t v___x_3001_; 
v___x_3001_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2996_);
lean_dec_ref(v___x_2996_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v_toGoalState_3003_; lean_object* v_enodeMap_3004_; lean_object* v_congrTable_3005_; lean_object* v___x_3006_; 
v___x_3002_ = lean_st_ref_get(v___y_2932_);
v_toGoalState_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc_ref(v_toGoalState_3003_);
lean_dec(v___x_3002_);
v_enodeMap_3004_ = lean_ctor_get(v_toGoalState_3003_, 1);
lean_inc_ref(v_enodeMap_3004_);
v_congrTable_3005_ = lean_ctor_get(v_toGoalState_3003_, 4);
lean_inc_ref(v_congrTable_3005_);
lean_dec_ref(v_toGoalState_3003_);
lean_inc_ref(v_self_2950_);
v___x_3006_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3004_, v_congrTable_3005_, v_self_2950_);
lean_dec_ref(v_congrTable_3005_);
lean_dec_ref(v_enodeMap_3004_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_dec(v_ematchDiagSource_2966_);
lean_dec(v_sTerms_2964_);
lean_dec(v_mt_2963_);
lean_dec(v_generation_2962_);
lean_dec(v_idx_2961_);
lean_dec(v_size_2956_);
lean_dec(v_proof_x3f_2954_);
lean_dec(v_target_x3f_2953_);
lean_dec_ref(v_self_2950_);
goto v___jp_2970_;
}
else
{
lean_object* v_val_3007_; lean_object* v_fst_3008_; lean_object* v___x_3009_; 
v_val_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_val_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v_fst_3008_ = lean_ctor_get(v_val_3007_, 0);
lean_inc(v_fst_3008_);
lean_dec(v_val_3007_);
v___x_3009_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3008_, v___y_2933_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; uint8_t v___x_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3011_ = lean_unbox(v_a_3010_);
lean_dec(v_a_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; lean_object* v_toGoalState_3013_; lean_object* v_mvarId_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3088_; 
v___x_3012_ = lean_st_ref_take(v___y_2932_);
v_toGoalState_3013_ = lean_ctor_get(v___x_3012_, 0);
v_mvarId_3014_ = lean_ctor_get(v___x_3012_, 1);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3016_ = v___x_3012_;
v_isShared_3017_ = v_isSharedCheck_3088_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_mvarId_3014_);
lean_inc(v_toGoalState_3013_);
lean_dec(v___x_3012_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3088_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v_nextDeclIdx_3018_; lean_object* v_enodeMap_3019_; lean_object* v_exprs_3020_; lean_object* v_parents_3021_; lean_object* v_congrTable_3022_; lean_object* v_appMap_3023_; lean_object* v_indicesFound_3024_; lean_object* v_newFacts_3025_; uint8_t v_inconsistent_3026_; lean_object* v_nextIdx_3027_; lean_object* v_newRawFacts_3028_; lean_object* v_facts_3029_; lean_object* v_extThms_3030_; lean_object* v_ematch_3031_; lean_object* v_inj_3032_; lean_object* v_split_3033_; lean_object* v_clean_3034_; lean_object* v_sstates_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3087_; 
v_nextDeclIdx_3018_ = lean_ctor_get(v_toGoalState_3013_, 0);
v_enodeMap_3019_ = lean_ctor_get(v_toGoalState_3013_, 1);
v_exprs_3020_ = lean_ctor_get(v_toGoalState_3013_, 2);
v_parents_3021_ = lean_ctor_get(v_toGoalState_3013_, 3);
v_congrTable_3022_ = lean_ctor_get(v_toGoalState_3013_, 4);
v_appMap_3023_ = lean_ctor_get(v_toGoalState_3013_, 5);
v_indicesFound_3024_ = lean_ctor_get(v_toGoalState_3013_, 6);
v_newFacts_3025_ = lean_ctor_get(v_toGoalState_3013_, 7);
v_inconsistent_3026_ = lean_ctor_get_uint8(v_toGoalState_3013_, sizeof(void*)*17);
v_nextIdx_3027_ = lean_ctor_get(v_toGoalState_3013_, 8);
v_newRawFacts_3028_ = lean_ctor_get(v_toGoalState_3013_, 9);
v_facts_3029_ = lean_ctor_get(v_toGoalState_3013_, 10);
v_extThms_3030_ = lean_ctor_get(v_toGoalState_3013_, 11);
v_ematch_3031_ = lean_ctor_get(v_toGoalState_3013_, 12);
v_inj_3032_ = lean_ctor_get(v_toGoalState_3013_, 13);
v_split_3033_ = lean_ctor_get(v_toGoalState_3013_, 14);
v_clean_3034_ = lean_ctor_get(v_toGoalState_3013_, 15);
v_sstates_3035_ = lean_ctor_get(v_toGoalState_3013_, 16);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_toGoalState_3013_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3037_ = v_toGoalState_3013_;
v_isShared_3038_ = v_isSharedCheck_3087_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_sstates_3035_);
lean_inc(v_clean_3034_);
lean_inc(v_split_3033_);
lean_inc(v_inj_3032_);
lean_inc(v_ematch_3031_);
lean_inc(v_extThms_3030_);
lean_inc(v_facts_3029_);
lean_inc(v_newRawFacts_3028_);
lean_inc(v_nextIdx_3027_);
lean_inc(v_newFacts_3025_);
lean_inc(v_indicesFound_3024_);
lean_inc(v_appMap_3023_);
lean_inc(v_congrTable_3022_);
lean_inc(v_parents_3021_);
lean_inc(v_exprs_3020_);
lean_inc(v_enodeMap_3019_);
lean_inc(v_nextDeclIdx_3018_);
lean_dec(v_toGoalState_3013_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3087_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3039_ = lean_box(0);
lean_inc_ref(v_self_2950_);
v___x_3040_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3019_, v_congrTable_3022_, v_self_2950_, v___x_3039_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 4, v___x_3040_);
v___x_3042_ = v___x_3037_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_nextDeclIdx_3018_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_enodeMap_3019_);
lean_ctor_set(v_reuseFailAlloc_3086_, 2, v_exprs_3020_);
lean_ctor_set(v_reuseFailAlloc_3086_, 3, v_parents_3021_);
lean_ctor_set(v_reuseFailAlloc_3086_, 4, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3086_, 5, v_appMap_3023_);
lean_ctor_set(v_reuseFailAlloc_3086_, 6, v_indicesFound_3024_);
lean_ctor_set(v_reuseFailAlloc_3086_, 7, v_newFacts_3025_);
lean_ctor_set(v_reuseFailAlloc_3086_, 8, v_nextIdx_3027_);
lean_ctor_set(v_reuseFailAlloc_3086_, 9, v_newRawFacts_3028_);
lean_ctor_set(v_reuseFailAlloc_3086_, 10, v_facts_3029_);
lean_ctor_set(v_reuseFailAlloc_3086_, 11, v_extThms_3030_);
lean_ctor_set(v_reuseFailAlloc_3086_, 12, v_ematch_3031_);
lean_ctor_set(v_reuseFailAlloc_3086_, 13, v_inj_3032_);
lean_ctor_set(v_reuseFailAlloc_3086_, 14, v_split_3033_);
lean_ctor_set(v_reuseFailAlloc_3086_, 15, v_clean_3034_);
lean_ctor_set(v_reuseFailAlloc_3086_, 16, v_sstates_3035_);
lean_ctor_set_uint8(v_reuseFailAlloc_3086_, sizeof(void*)*17, v_inconsistent_3026_);
v___x_3042_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3044_; 
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3042_);
v___x_3044_ = v___x_3016_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3042_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_mvarId_3014_);
v___x_3044_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_st_ref_put(v___y_2932_, v___x_3044_);
lean_inc_ref(v_rootNew_2929_);
lean_inc_ref(v_next_2951_);
lean_inc_ref_n(v_self_2950_, 3);
v___x_3046_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3046_, 0, v_self_2950_);
lean_ctor_set(v___x_3046_, 1, v_next_2951_);
lean_ctor_set(v___x_3046_, 2, v_rootNew_2929_);
lean_ctor_set(v___x_3046_, 3, v_self_2950_);
lean_ctor_set(v___x_3046_, 4, v_target_x3f_2953_);
lean_ctor_set(v___x_3046_, 5, v_proof_x3f_2954_);
lean_ctor_set(v___x_3046_, 6, v_size_2956_);
lean_ctor_set(v___x_3046_, 7, v_idx_2961_);
lean_ctor_set(v___x_3046_, 8, v_generation_2962_);
lean_ctor_set(v___x_3046_, 9, v_mt_2963_);
lean_ctor_set(v___x_3046_, 10, v_sTerms_2964_);
lean_ctor_set(v___x_3046_, 11, v_ematchDiagSource_2966_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*12, v_flipped_2955_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*12 + 1, v_interpreted_2957_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*12 + 2, v_ctor_2958_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*12 + 3, v_hasLambdas_2959_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*12 + 4, v_heqProofs_2960_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*12 + 5, v_funCC_2965_);
v___x_3047_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2950_, v___x_3046_, v___y_2932_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_dec_ref_known(v___x_3047_, 1);
v___x_3048_ = lean_st_ref_get(v___y_2932_);
lean_inc(v_fst_3008_);
v___x_3049_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3048_, v_fst_3008_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___x_3048_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v_self_3051_; lean_object* v_next_3052_; lean_object* v_root_3053_; lean_object* v_target_x3f_3054_; lean_object* v_proof_x3f_3055_; uint8_t v_flipped_3056_; lean_object* v_size_3057_; uint8_t v_interpreted_3058_; uint8_t v_ctor_3059_; uint8_t v_hasLambdas_3060_; uint8_t v_heqProofs_3061_; lean_object* v_idx_3062_; lean_object* v_generation_3063_; lean_object* v_mt_3064_; lean_object* v_sTerms_3065_; uint8_t v_funCC_3066_; lean_object* v_ematchDiagSource_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3075_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref_known(v___x_3049_, 1);
v_self_3051_ = lean_ctor_get(v_a_3050_, 0);
v_next_3052_ = lean_ctor_get(v_a_3050_, 1);
v_root_3053_ = lean_ctor_get(v_a_3050_, 2);
v_target_x3f_3054_ = lean_ctor_get(v_a_3050_, 4);
v_proof_x3f_3055_ = lean_ctor_get(v_a_3050_, 5);
v_flipped_3056_ = lean_ctor_get_uint8(v_a_3050_, sizeof(void*)*12);
v_size_3057_ = lean_ctor_get(v_a_3050_, 6);
v_interpreted_3058_ = lean_ctor_get_uint8(v_a_3050_, sizeof(void*)*12 + 1);
v_ctor_3059_ = lean_ctor_get_uint8(v_a_3050_, sizeof(void*)*12 + 2);
v_hasLambdas_3060_ = lean_ctor_get_uint8(v_a_3050_, sizeof(void*)*12 + 3);
v_heqProofs_3061_ = lean_ctor_get_uint8(v_a_3050_, sizeof(void*)*12 + 4);
v_idx_3062_ = lean_ctor_get(v_a_3050_, 7);
v_generation_3063_ = lean_ctor_get(v_a_3050_, 8);
v_mt_3064_ = lean_ctor_get(v_a_3050_, 9);
v_sTerms_3065_ = lean_ctor_get(v_a_3050_, 10);
v_funCC_3066_ = lean_ctor_get_uint8(v_a_3050_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3067_ = lean_ctor_get(v_a_3050_, 11);
v_isSharedCheck_3075_ = !lean_is_exclusive(v_a_3050_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; 
v_unused_3076_ = lean_ctor_get(v_a_3050_, 3);
lean_dec(v_unused_3076_);
v___x_3069_ = v_a_3050_;
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_ematchDiagSource_3067_);
lean_inc(v_sTerms_3065_);
lean_inc(v_mt_3064_);
lean_inc(v_generation_3063_);
lean_inc(v_idx_3062_);
lean_inc(v_size_3057_);
lean_inc(v_proof_x3f_3055_);
lean_inc(v_target_x3f_3054_);
lean_inc(v_root_3053_);
lean_inc(v_next_3052_);
lean_inc(v_self_3051_);
lean_dec(v_a_3050_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 3, v_self_2950_);
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_self_3051_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_next_3052_);
lean_ctor_set(v_reuseFailAlloc_3074_, 2, v_root_3053_);
lean_ctor_set(v_reuseFailAlloc_3074_, 3, v_self_2950_);
lean_ctor_set(v_reuseFailAlloc_3074_, 4, v_target_x3f_3054_);
lean_ctor_set(v_reuseFailAlloc_3074_, 5, v_proof_x3f_3055_);
lean_ctor_set(v_reuseFailAlloc_3074_, 6, v_size_3057_);
lean_ctor_set(v_reuseFailAlloc_3074_, 7, v_idx_3062_);
lean_ctor_set(v_reuseFailAlloc_3074_, 8, v_generation_3063_);
lean_ctor_set(v_reuseFailAlloc_3074_, 9, v_mt_3064_);
lean_ctor_set(v_reuseFailAlloc_3074_, 10, v_sTerms_3065_);
lean_ctor_set(v_reuseFailAlloc_3074_, 11, v_ematchDiagSource_3067_);
lean_ctor_set_uint8(v_reuseFailAlloc_3074_, sizeof(void*)*12, v_flipped_3056_);
lean_ctor_set_uint8(v_reuseFailAlloc_3074_, sizeof(void*)*12 + 1, v_interpreted_3058_);
lean_ctor_set_uint8(v_reuseFailAlloc_3074_, sizeof(void*)*12 + 2, v_ctor_3059_);
lean_ctor_set_uint8(v_reuseFailAlloc_3074_, sizeof(void*)*12 + 3, v_hasLambdas_3060_);
lean_ctor_set_uint8(v_reuseFailAlloc_3074_, sizeof(void*)*12 + 4, v_heqProofs_3061_);
lean_ctor_set_uint8(v_reuseFailAlloc_3074_, sizeof(void*)*12 + 5, v_funCC_3066_);
v___x_3072_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3008_, v___x_3072_, v___y_2932_);
v___y_2986_ = v___x_3073_;
goto v___jp_2985_;
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v_fst_3008_);
lean_dec_ref(v_next_2951_);
lean_dec_ref(v_self_2950_);
lean_del_object(v___x_2948_);
lean_del_object(v___x_2941_);
lean_dec(v_snd_2939_);
lean_dec_ref(v_rootNew_2929_);
v_a_3077_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3049_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3049_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_dec(v_fst_3008_);
lean_dec_ref(v_self_2950_);
v___y_2986_ = v___x_3047_;
goto v___jp_2985_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3008_);
lean_dec(v_ematchDiagSource_2966_);
lean_dec(v_sTerms_2964_);
lean_dec(v_mt_2963_);
lean_dec(v_generation_2962_);
lean_dec(v_idx_2961_);
lean_dec(v_size_2956_);
lean_dec(v_proof_x3f_2954_);
lean_dec(v_target_x3f_2953_);
lean_dec_ref(v_self_2950_);
goto v___jp_2970_;
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_fst_3008_);
lean_dec(v_ematchDiagSource_2966_);
lean_dec(v_sTerms_2964_);
lean_dec(v_mt_2963_);
lean_dec(v_generation_2962_);
lean_dec(v_idx_2961_);
lean_dec(v_size_2956_);
lean_dec(v_proof_x3f_2954_);
lean_dec(v_target_x3f_2953_);
lean_dec_ref(v_next_2951_);
lean_dec_ref(v_self_2950_);
lean_del_object(v___x_2948_);
lean_del_object(v___x_2941_);
lean_dec(v_snd_2939_);
lean_dec_ref(v_rootNew_2929_);
v_a_3089_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3009_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3009_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2966_);
lean_dec(v_sTerms_2964_);
lean_dec(v_mt_2963_);
lean_dec(v_generation_2962_);
lean_dec(v_idx_2961_);
lean_dec(v_size_2956_);
lean_dec(v_proof_x3f_2954_);
lean_dec(v_target_x3f_2953_);
lean_dec_ref(v_self_2950_);
goto v___jp_2970_;
}
}
}
}
else
{
lean_dec_ref(v___x_2996_);
lean_dec(v_ematchDiagSource_2966_);
lean_dec(v_sTerms_2964_);
lean_dec(v_mt_2963_);
lean_dec(v_generation_2962_);
lean_dec(v_idx_2961_);
lean_dec(v_size_2956_);
lean_dec(v_proof_x3f_2954_);
lean_dec(v_target_x3f_2953_);
lean_dec_ref(v_self_2950_);
v___y_2986_ = v___x_2997_;
goto v___jp_2985_;
}
}
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_del_object(v___x_2941_);
lean_dec(v_snd_2939_);
lean_dec_ref(v_rootNew_2929_);
v_a_3101_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_2945_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_2945_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3111_, lean_object* v_rootNew_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
uint8_t v_a_26289__boxed_3122_; lean_object* v_res_3123_; 
v_a_26289__boxed_3122_ = lean_unbox(v_a_3113_);
v_res_3123_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3111_, v_rootNew_3112_, v_a_26289__boxed_3122_, v_a_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v_lhs_3111_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3124_, lean_object* v_rootNew_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3125_, v_a_3130_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; lean_object* v___x_3142_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v___x_3139_ = lean_box(0);
lean_inc_ref(v_lhs_3124_);
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
lean_ctor_set(v___x_3140_, 1, v_lhs_3124_);
v___x_3141_ = lean_unbox(v_a_3138_);
lean_dec(v_a_3138_);
v___x_3142_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3124_, v_rootNew_3125_, v___x_3141_, v___x_3140_, v_a_3126_, v_a_3130_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
lean_dec_ref(v_lhs_3124_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3156_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3156_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3156_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v_fst_3147_; 
v_fst_3147_ = lean_ctor_get(v_a_3143_, 0);
lean_inc(v_fst_3147_);
lean_dec(v_a_3143_);
if (lean_obj_tag(v_fst_3147_) == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3150_; 
v___x_3148_ = lean_box(0);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v___x_3148_);
v___x_3150_ = v___x_3145_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3148_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
else
{
lean_object* v_val_3152_; lean_object* v___x_3154_; 
v_val_3152_ = lean_ctor_get(v_fst_3147_, 0);
lean_inc(v_val_3152_);
lean_dec_ref_known(v_fst_3147_, 1);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v_val_3152_);
v___x_3154_ = v___x_3145_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_val_3152_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
v_a_3157_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3142_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3142_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec_ref(v_rootNew_3125_);
lean_dec_ref(v_lhs_3124_);
v_a_3165_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3137_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3137_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3173_, lean_object* v_rootNew_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3173_, v_rootNew_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec(v_a_3175_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3187_, lean_object* v_00_u03b2_3188_, lean_object* v_x_3189_, lean_object* v_x_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3187_, v_x_3189_, v_x_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3192_, lean_object* v_00_u03b2_3193_, lean_object* v_x_3194_, lean_object* v_x_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3192_, v_00_u03b2_3193_, v_x_3194_, v_x_3195_);
lean_dec_ref(v_x_3194_);
lean_dec_ref(v___x_3192_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3197_, lean_object* v_00_u03b2_3198_, lean_object* v_x_3199_, lean_object* v_x_3200_, lean_object* v_x_3201_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3197_, v_x_3199_, v_x_3200_, v_x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3203_, lean_object* v_00_u03b2_3204_, lean_object* v_x_3205_, lean_object* v_x_3206_, lean_object* v_x_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3203_, v_00_u03b2_3204_, v_x_3205_, v_x_3206_, v_x_3207_);
lean_dec_ref(v___x_3203_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3209_, lean_object* v_rootNew_3210_, uint8_t v_a_3211_, lean_object* v_inst_3212_, lean_object* v_a_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3209_, v_rootNew_3210_, v_a_3211_, v_a_3213_, v___y_3214_, v___y_3218_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3226_, lean_object* v_rootNew_3227_, lean_object* v_a_3228_, lean_object* v_inst_3229_, lean_object* v_a_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
uint8_t v_a_26648__boxed_3242_; lean_object* v_res_3243_; 
v_a_26648__boxed_3242_ = lean_unbox(v_a_3228_);
v_res_3243_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3226_, v_rootNew_3227_, v_a_26648__boxed_3242_, v_inst_3229_, v_a_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v_lhs_3226_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3244_, lean_object* v_00_u03b2_3245_, lean_object* v_x_3246_, size_t v_x_3247_, lean_object* v_x_3248_){
_start:
{
lean_object* v___x_3249_; 
lean_inc_ref(v_x_3246_);
v___x_3249_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3244_, v_x_3246_, v_x_3247_, v_x_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3250_, lean_object* v_00_u03b2_3251_, lean_object* v_x_3252_, lean_object* v_x_3253_, lean_object* v_x_3254_){
_start:
{
size_t v_x_26691__boxed_3255_; lean_object* v_res_3256_; 
v_x_26691__boxed_3255_ = lean_unbox_usize(v_x_3253_);
lean_dec(v_x_3253_);
v_res_3256_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3250_, v_00_u03b2_3251_, v_x_3252_, v_x_26691__boxed_3255_, v_x_3254_);
lean_dec_ref(v_x_3252_);
lean_dec_ref(v___x_3250_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3257_, lean_object* v_00_u03b2_3258_, lean_object* v_x_3259_, size_t v_x_3260_, size_t v_x_3261_, lean_object* v_x_3262_, lean_object* v_x_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3257_, v_x_3259_, v_x_3260_, v_x_3261_, v_x_3262_, v_x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3265_, lean_object* v_00_u03b2_3266_, lean_object* v_x_3267_, lean_object* v_x_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_){
_start:
{
size_t v_x_26705__boxed_3272_; size_t v_x_26706__boxed_3273_; lean_object* v_res_3274_; 
v_x_26705__boxed_3272_ = lean_unbox_usize(v_x_3268_);
lean_dec(v_x_3268_);
v_x_26706__boxed_3273_ = lean_unbox_usize(v_x_3269_);
lean_dec(v_x_3269_);
v_res_3274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3265_, v_00_u03b2_3266_, v_x_3267_, v_x_26705__boxed_3272_, v_x_26706__boxed_3273_, v_x_3270_, v_x_3271_);
lean_dec_ref(v___x_3265_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3275_, lean_object* v_00_u03b2_3276_, lean_object* v_keys_3277_, lean_object* v_vals_3278_, lean_object* v_heq_3279_, lean_object* v_i_3280_, lean_object* v_k_3281_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3275_, v_keys_3277_, v_vals_3278_, v_i_3280_, v_k_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3283_, lean_object* v_00_u03b2_3284_, lean_object* v_keys_3285_, lean_object* v_vals_3286_, lean_object* v_heq_3287_, lean_object* v_i_3288_, lean_object* v_k_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3283_, v_00_u03b2_3284_, v_keys_3285_, v_vals_3286_, v_heq_3287_, v_i_3288_, v_k_3289_);
lean_dec_ref(v_vals_3286_);
lean_dec_ref(v_keys_3285_);
lean_dec_ref(v___x_3283_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3291_, lean_object* v_00_u03b2_3292_, lean_object* v_n_3293_, lean_object* v_k_3294_, lean_object* v_v_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3291_, v_n_3293_, v_k_3294_, v_v_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3297_, lean_object* v_00_u03b2_3298_, lean_object* v_n_3299_, lean_object* v_k_3300_, lean_object* v_v_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3297_, v_00_u03b2_3298_, v_n_3299_, v_k_3300_, v_v_3301_);
lean_dec_ref(v___x_3297_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3303_, lean_object* v_00_u03b2_3304_, size_t v_depth_3305_, lean_object* v_keys_3306_, lean_object* v_vals_3307_, lean_object* v_heq_3308_, lean_object* v_i_3309_, lean_object* v_entries_3310_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3303_, v_depth_3305_, v_keys_3306_, v_vals_3307_, v_i_3309_, v_entries_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3312_, lean_object* v_00_u03b2_3313_, lean_object* v_depth_3314_, lean_object* v_keys_3315_, lean_object* v_vals_3316_, lean_object* v_heq_3317_, lean_object* v_i_3318_, lean_object* v_entries_3319_){
_start:
{
size_t v_depth_boxed_3320_; lean_object* v_res_3321_; 
v_depth_boxed_3320_ = lean_unbox_usize(v_depth_3314_);
lean_dec(v_depth_3314_);
v_res_3321_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3312_, v_00_u03b2_3313_, v_depth_boxed_3320_, v_keys_3315_, v_vals_3316_, v_heq_3317_, v_i_3318_, v_entries_3319_);
lean_dec_ref(v_vals_3316_);
lean_dec_ref(v_keys_3315_);
lean_dec_ref(v___x_3312_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3322_, lean_object* v_00_u03b2_3323_, lean_object* v_x_3324_, lean_object* v_x_3325_, lean_object* v_x_3326_, lean_object* v_x_3327_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3322_, v_x_3324_, v_x_3325_, v_x_3326_, v_x_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3329_, lean_object* v_00_u03b2_3330_, lean_object* v_x_3331_, lean_object* v_x_3332_, lean_object* v_x_3333_, lean_object* v_x_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3329_, v_00_u03b2_3330_, v_x_3331_, v_x_3332_, v_x_3333_, v_x_3334_);
lean_dec_ref(v___x_3329_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3336_, lean_object* v_b_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
if (lean_obj_tag(v_as_x27_3336_) == 0)
{
lean_object* v___x_3349_; 
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_b_3337_);
return v___x_3349_;
}
else
{
lean_object* v_head_3350_; lean_object* v_tail_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v_head_3350_ = lean_ctor_get(v_as_x27_3336_, 0);
v_tail_3351_ = lean_ctor_get(v_as_x27_3336_, 1);
v___x_3352_ = lean_box(0);
lean_inc(v_head_3350_);
v___x_3353_ = l_Lean_Meta_Grind_propagateUp(v_head_3350_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_dec_ref_known(v___x_3353_, 1);
v_as_x27_3336_ = v_tail_3351_;
v_b_3337_ = v___x_3352_;
goto _start;
}
else
{
return v___x_3353_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3355_, lean_object* v_b_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3355_, v_b_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec(v_as_x27_3355_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3369_, lean_object* v_b_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
if (lean_obj_tag(v_as_x27_3369_) == 0)
{
lean_object* v___x_3382_; 
v___x_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3382_, 0, v_b_3370_);
return v___x_3382_;
}
else
{
lean_object* v_head_3383_; lean_object* v_tail_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v_head_3383_ = lean_ctor_get(v_as_x27_3369_, 0);
v_tail_3384_ = lean_ctor_get(v_as_x27_3369_, 1);
v___x_3385_ = lean_box(0);
lean_inc(v_head_3383_);
v___x_3386_ = l_Lean_Meta_Grind_propagateDown(v_head_3383_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_dec_ref_known(v___x_3386_, 1);
v_as_x27_3369_ = v_tail_3384_;
v_b_3370_ = v___x_3385_;
goto _start;
}
else
{
return v___x_3386_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3388_, lean_object* v_b_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3388_, v_b_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec(v_as_x27_3388_);
return v_res_3401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_cls_3405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3406_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3407_ = l_Lean_Name_append(v___x_3406_, v_cls_3405_);
return v___x_3407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
return v___x_3410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3413_ = l_Lean_stringToMessageData(v___x_3412_);
return v___x_3413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3416_ = l_Lean_stringToMessageData(v___x_3415_);
return v___x_3416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3419_ = l_Lean_stringToMessageData(v___x_3418_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3420_, uint8_t v_isHEq_3421_, lean_object* v_lhs_3422_, lean_object* v_rhs_3423_, lean_object* v_lhsNode_3424_, lean_object* v_rhsNode_3425_, lean_object* v_lhsRoot_3426_, lean_object* v_rhsRoot_3427_, uint8_t v_flipped_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_){
_start:
{
lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; uint8_t v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; uint8_t v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3526_; uint8_t v___y_3527_; uint8_t v___y_3528_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; uint8_t v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; uint8_t v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; uint8_t v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; uint8_t v___y_3589_; uint8_t v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; uint8_t v___y_3593_; uint8_t v___y_3594_; uint8_t v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; uint8_t v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v_toCold_3678_; lean_object* v_options_3679_; lean_object* v_inheritedTraceOptions_3680_; uint8_t v_hasTrace_3681_; lean_object* v_cls_3682_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v_fns_u2082_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v_fns_u2081_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; 
v_toCold_3678_ = lean_ctor_get(v_a_3437_, 0);
v_options_3679_ = lean_ctor_get(v_toCold_3678_, 2);
v_inheritedTraceOptions_3680_ = lean_ctor_get(v_toCold_3678_, 11);
v_hasTrace_3681_ = lean_ctor_get_uint8(v_options_3679_, sizeof(void*)*1);
v_cls_3682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3681_ == 0)
{
v___y_3802_ = v_a_3429_;
v___y_3803_ = v_a_3430_;
v___y_3804_ = v_a_3431_;
v___y_3805_ = v_a_3432_;
v___y_3806_ = v_a_3433_;
v___y_3807_ = v_a_3434_;
v___y_3808_ = v_a_3435_;
v___y_3809_ = v_a_3436_;
v___y_3810_ = v_a_3437_;
v___y_3811_ = v_a_3438_;
goto v___jp_3801_;
}
else
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3882_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3883_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3680_, v_options_3679_, v___x_3882_);
if (v___x_3883_ == 0)
{
v___y_3802_ = v_a_3429_;
v___y_3803_ = v_a_3430_;
v___y_3804_ = v_a_3431_;
v___y_3805_ = v_a_3432_;
v___y_3806_ = v_a_3433_;
v___y_3807_ = v_a_3434_;
v___y_3808_ = v_a_3435_;
v___y_3809_ = v_a_3436_;
v___y_3810_ = v_a_3437_;
v___y_3811_ = v_a_3438_;
goto v___jp_3801_;
}
else
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_Meta_Grind_updateLastTag(v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v___x_3885_; 
lean_dec_ref_known(v___x_3884_, 1);
lean_inc_ref(v_lhs_3422_);
v___x_3885_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3422_, v_a_3429_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3887_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
lean_inc_ref(v_rhs_3423_);
v___x_3887_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3423_, v_a_3429_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
v___x_3889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
lean_ctor_set(v___x_3890_, 1, v_a_3886_);
v___x_3891_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3890_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v_a_3888_);
v___x_3894_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3682_, v___x_3893_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_dec_ref_known(v___x_3894_, 1);
v___y_3802_ = v_a_3429_;
v___y_3803_ = v_a_3430_;
v___y_3804_ = v_a_3431_;
v___y_3805_ = v_a_3432_;
v___y_3806_ = v_a_3433_;
v___y_3807_ = v_a_3434_;
v___y_3808_ = v_a_3435_;
v___y_3809_ = v_a_3436_;
v___y_3810_ = v_a_3437_;
v___y_3811_ = v_a_3438_;
goto v___jp_3801_;
}
else
{
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhsNode_3424_);
lean_dec_ref(v_rhs_3423_);
lean_dec_ref(v_lhs_3422_);
lean_dec_ref(v_proof_3420_);
return v___x_3894_;
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_dec(v_a_3886_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhsNode_3424_);
lean_dec_ref(v_rhs_3423_);
lean_dec_ref(v_lhs_3422_);
lean_dec_ref(v_proof_3420_);
v_a_3895_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3887_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3887_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhsNode_3424_);
lean_dec_ref(v_rhs_3423_);
lean_dec_ref(v_lhs_3422_);
lean_dec_ref(v_proof_3420_);
v_a_3903_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3885_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3885_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhsNode_3424_);
lean_dec_ref(v_rhs_3423_);
lean_dec_ref(v_lhs_3422_);
lean_dec_ref(v_proof_3420_);
return v___x_3884_;
}
}
}
v___jp_3440_:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3447_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3483_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3460_ = v___x_3457_;
v_isShared_3461_ = v_isSharedCheck_3483_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3483_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
uint8_t v___x_3462_; 
v___x_3462_ = lean_unbox(v_a_3458_);
lean_dec(v_a_3458_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_del_object(v___x_3460_);
v___x_3463_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3446_);
lean_dec(v___y_3446_);
v___x_3464_ = lean_box(0);
v___x_3465_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3463_, v___x_3464_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___x_3463_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v___x_3466_; 
lean_dec_ref_known(v___x_3465_, 1);
v___x_3466_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3442_, v___x_3464_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3467_; 
lean_dec_ref_known(v___x_3466_, 1);
v___x_3467_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3441_, v___y_3445_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec_ref(v___y_3445_);
lean_dec_ref(v___y_3441_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3468_; 
lean_dec_ref_known(v___x_3467_, 1);
v___x_3468_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3443_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3477_; 
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3468_, 0);
lean_dec(v_unused_3478_);
v___x_3470_ = v___x_3468_;
v_isShared_3471_ = v_isSharedCheck_3477_;
goto v_resetjp_3469_;
}
else
{
lean_dec(v___x_3468_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3477_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
uint8_t v___x_3472_; 
v___x_3472_ = l_Lean_Expr_isTrue(v___y_3444_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3474_; 
lean_dec(v___y_3442_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3464_);
v___x_3474_ = v___x_3470_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3464_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
else
{
lean_object* v___x_3476_; 
lean_del_object(v___x_3470_);
v___x_3476_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3442_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3442_);
return v___x_3476_;
}
}
}
else
{
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3442_);
return v___x_3468_;
}
}
else
{
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
return v___x_3467_;
}
}
else
{
lean_dec_ref(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
return v___x_3466_;
}
}
else
{
lean_dec_ref(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
return v___x_3465_;
}
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
v___x_3479_ = lean_box(0);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3479_);
v___x_3481_ = v___x_3460_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
v_a_3484_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3457_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3457_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
v___jp_3492_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_inc_ref(v___y_3501_);
v___x_3529_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3529_, 0, v___y_3501_);
lean_ctor_set(v___x_3529_, 1, v___y_3499_);
lean_ctor_set(v___x_3529_, 2, v___y_3518_);
lean_ctor_set(v___x_3529_, 3, v___y_3520_);
lean_ctor_set(v___x_3529_, 4, v___y_3525_);
lean_ctor_set(v___x_3529_, 5, v___y_3517_);
lean_ctor_set(v___x_3529_, 6, v___y_3511_);
lean_ctor_set(v___x_3529_, 7, v___y_3516_);
lean_ctor_set(v___x_3529_, 8, v___y_3510_);
lean_ctor_set(v___x_3529_, 9, v___y_3493_);
lean_ctor_set(v___x_3529_, 10, v___y_3500_);
lean_ctor_set(v___x_3529_, 11, v___y_3513_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*12, v___y_3523_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*12 + 1, v___y_3497_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*12 + 2, v___y_3527_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*12 + 3, v___y_3515_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*12 + 4, v___y_3528_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*12 + 5, v___y_3526_);
lean_inc_ref(v___y_3502_);
v___x_3530_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3502_, v___x_3529_, v___y_3496_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v___x_3531_; 
lean_dec_ref_known(v___x_3530_, 1);
lean_inc_ref(v___y_3512_);
v___x_3531_ = l_Lean_Meta_Grind_propagateBeta(v___y_3512_, v___y_3521_, v___y_3496_, v___y_3514_, v___y_3507_, v___y_3503_, v___y_3522_, v___y_3506_, v___y_3495_, v___y_3505_, v___y_3519_, v___y_3509_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v___x_3532_; 
lean_dec_ref_known(v___x_3531_, 1);
lean_inc_ref(v___y_3524_);
v___x_3532_ = l_Lean_Meta_Grind_propagateBeta(v___y_3524_, v___y_3494_, v___y_3496_, v___y_3514_, v___y_3507_, v___y_3503_, v___y_3522_, v___y_3506_, v___y_3495_, v___y_3505_, v___y_3519_, v___y_3509_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v___x_3533_; 
lean_dec_ref_known(v___x_3532_, 1);
v___x_3533_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3427_, v_lhsRoot_3426_, v___y_3496_, v___y_3495_, v___y_3505_, v___y_3519_, v___y_3509_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3535_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v___x_3535_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3498_, v___y_3496_);
lean_dec_ref(v___y_3498_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v___x_3536_; 
lean_dec_ref_known(v___x_3535_, 1);
lean_inc_ref(v___y_3502_);
v___x_3536_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3508_, v___y_3502_, v___y_3496_, v___y_3514_, v___y_3507_, v___y_3503_, v___y_3522_, v___y_3506_, v___y_3495_, v___y_3505_, v___y_3519_, v___y_3509_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v___x_3537_; 
lean_dec_ref_known(v___x_3536_, 1);
v___x_3537_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3496_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; uint8_t v___x_3539_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref_known(v___x_3537_, 1);
v___x_3539_ = lean_unbox(v_a_3538_);
lean_dec(v_a_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; 
v___x_3540_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3501_, v___y_3496_, v___y_3514_, v___y_3507_, v___y_3503_, v___y_3522_, v___y_3506_, v___y_3495_, v___y_3505_, v___y_3519_, v___y_3509_);
lean_dec_ref(v___y_3501_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_dec_ref_known(v___x_3540_, 1);
v___y_3441_ = v___y_3512_;
v___y_3442_ = v___y_3504_;
v___y_3443_ = v_a_3534_;
v___y_3444_ = v___y_3502_;
v___y_3445_ = v___y_3524_;
v___y_3446_ = v___y_3508_;
v___y_3447_ = v___y_3496_;
v___y_3448_ = v___y_3514_;
v___y_3449_ = v___y_3507_;
v___y_3450_ = v___y_3503_;
v___y_3451_ = v___y_3522_;
v___y_3452_ = v___y_3506_;
v___y_3453_ = v___y_3495_;
v___y_3454_ = v___y_3505_;
v___y_3455_ = v___y_3519_;
v___y_3456_ = v___y_3509_;
goto v___jp_3440_;
}
else
{
lean_dec(v_a_3534_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3502_);
return v___x_3540_;
}
}
else
{
lean_dec_ref(v___y_3501_);
v___y_3441_ = v___y_3512_;
v___y_3442_ = v___y_3504_;
v___y_3443_ = v_a_3534_;
v___y_3444_ = v___y_3502_;
v___y_3445_ = v___y_3524_;
v___y_3446_ = v___y_3508_;
v___y_3447_ = v___y_3496_;
v___y_3448_ = v___y_3514_;
v___y_3449_ = v___y_3507_;
v___y_3450_ = v___y_3503_;
v___y_3451_ = v___y_3522_;
v___y_3452_ = v___y_3506_;
v___y_3453_ = v___y_3495_;
v___y_3454_ = v___y_3505_;
v___y_3455_ = v___y_3519_;
v___y_3456_ = v___y_3509_;
goto v___jp_3440_;
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec(v_a_3534_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
v_a_3541_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3537_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3537_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
else
{
lean_dec(v_a_3534_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
return v___x_3536_;
}
}
else
{
lean_dec(v_a_3534_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
return v___x_3535_;
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v___y_3498_);
v_a_3549_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3533_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3533_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
else
{
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
return v___x_3532_;
}
}
else
{
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v___y_3494_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
return v___x_3531_;
}
}
else
{
lean_dec_ref(v___y_3524_);
lean_dec_ref(v___y_3521_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec_ref(v___y_3498_);
lean_dec_ref(v___y_3494_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
return v___x_3530_;
}
}
v___jp_3557_:
{
if (v_isHEq_3421_ == 0)
{
if (v___y_3567_ == 0)
{
v___y_3493_ = v___y_3558_;
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3561_;
v___y_3496_ = v___y_3560_;
v___y_3497_ = v___y_3562_;
v___y_3498_ = v___y_3565_;
v___y_3499_ = v___y_3564_;
v___y_3500_ = v___y_3563_;
v___y_3501_ = v___y_3566_;
v___y_3502_ = v___y_3568_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3571_;
v___y_3505_ = v___y_3572_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3574_;
v___y_3508_ = v___y_3575_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3577_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3594_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3587_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3585_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3592_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3590_;
v___y_3527_ = v___y_3593_;
v___y_3528_ = v___y_3570_;
goto v___jp_3492_;
}
else
{
v___y_3493_ = v___y_3558_;
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3561_;
v___y_3496_ = v___y_3560_;
v___y_3497_ = v___y_3562_;
v___y_3498_ = v___y_3565_;
v___y_3499_ = v___y_3564_;
v___y_3500_ = v___y_3563_;
v___y_3501_ = v___y_3566_;
v___y_3502_ = v___y_3568_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3571_;
v___y_3505_ = v___y_3572_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3574_;
v___y_3508_ = v___y_3575_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3577_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3594_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3587_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3585_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3592_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3590_;
v___y_3527_ = v___y_3593_;
v___y_3528_ = v___y_3567_;
goto v___jp_3492_;
}
}
else
{
v___y_3493_ = v___y_3558_;
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3561_;
v___y_3496_ = v___y_3560_;
v___y_3497_ = v___y_3562_;
v___y_3498_ = v___y_3565_;
v___y_3499_ = v___y_3564_;
v___y_3500_ = v___y_3563_;
v___y_3501_ = v___y_3566_;
v___y_3502_ = v___y_3568_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3571_;
v___y_3505_ = v___y_3572_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3574_;
v___y_3508_ = v___y_3575_;
v___y_3509_ = v___y_3576_;
v___y_3510_ = v___y_3577_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3594_;
v___y_3516_ = v___y_3582_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3584_;
v___y_3519_ = v___y_3587_;
v___y_3520_ = v___y_3586_;
v___y_3521_ = v___y_3585_;
v___y_3522_ = v___y_3588_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3592_;
v___y_3525_ = v___y_3591_;
v___y_3526_ = v___y_3590_;
v___y_3527_ = v___y_3593_;
v___y_3528_ = v_isHEq_3421_;
goto v___jp_3492_;
}
}
v___jp_3595_:
{
lean_object* v___x_3618_; 
v___x_3618_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3606_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3618_) == 0)
{
uint8_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
lean_dec_ref_known(v___x_3618_, 1);
v___x_3619_ = 0;
v___x_3620_ = lean_st_ref_get(v___y_3608_);
v___x_3621_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3620_, v_lhs_3422_, v___x_3619_);
lean_dec(v___x_3620_);
v___x_3622_ = lean_st_ref_get(v___y_3608_);
lean_inc_ref(v___y_3602_);
v___x_3623_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3622_, v___y_3602_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___x_3622_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v_self_3625_; lean_object* v_root_3626_; lean_object* v_congr_3627_; lean_object* v_target_x3f_3628_; lean_object* v_proof_x3f_3629_; uint8_t v_flipped_3630_; lean_object* v_size_3631_; uint8_t v_interpreted_3632_; uint8_t v_ctor_3633_; uint8_t v_hasLambdas_3634_; uint8_t v_heqProofs_3635_; lean_object* v_idx_3636_; lean_object* v_generation_3637_; lean_object* v_mt_3638_; lean_object* v_sTerms_3639_; uint8_t v_funCC_3640_; lean_object* v_ematchDiagSource_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3668_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v_self_3625_ = lean_ctor_get(v_a_3624_, 0);
v_root_3626_ = lean_ctor_get(v_a_3624_, 2);
v_congr_3627_ = lean_ctor_get(v_a_3624_, 3);
v_target_x3f_3628_ = lean_ctor_get(v_a_3624_, 4);
v_proof_x3f_3629_ = lean_ctor_get(v_a_3624_, 5);
v_flipped_3630_ = lean_ctor_get_uint8(v_a_3624_, sizeof(void*)*12);
v_size_3631_ = lean_ctor_get(v_a_3624_, 6);
v_interpreted_3632_ = lean_ctor_get_uint8(v_a_3624_, sizeof(void*)*12 + 1);
v_ctor_3633_ = lean_ctor_get_uint8(v_a_3624_, sizeof(void*)*12 + 2);
v_hasLambdas_3634_ = lean_ctor_get_uint8(v_a_3624_, sizeof(void*)*12 + 3);
v_heqProofs_3635_ = lean_ctor_get_uint8(v_a_3624_, sizeof(void*)*12 + 4);
v_idx_3636_ = lean_ctor_get(v_a_3624_, 7);
v_generation_3637_ = lean_ctor_get(v_a_3624_, 8);
v_mt_3638_ = lean_ctor_get(v_a_3624_, 9);
v_sTerms_3639_ = lean_ctor_get(v_a_3624_, 10);
v_funCC_3640_ = lean_ctor_get_uint8(v_a_3624_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3641_ = lean_ctor_get(v_a_3624_, 11);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_a_3624_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v_a_3624_, 1);
lean_dec(v_unused_3669_);
v___x_3643_ = v_a_3624_;
v_isShared_3644_ = v_isSharedCheck_3668_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_ematchDiagSource_3641_);
lean_inc(v_sTerms_3639_);
lean_inc(v_mt_3638_);
lean_inc(v_generation_3637_);
lean_inc(v_idx_3636_);
lean_inc(v_size_3631_);
lean_inc(v_proof_x3f_3629_);
lean_inc(v_target_x3f_3628_);
lean_inc(v_congr_3627_);
lean_inc(v_root_3626_);
lean_inc(v_self_3625_);
lean_dec(v_a_3624_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3668_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v_self_3645_; lean_object* v_next_3646_; lean_object* v_root_3647_; lean_object* v_congr_3648_; lean_object* v_target_x3f_3649_; lean_object* v_proof_x3f_3650_; uint8_t v_flipped_3651_; lean_object* v_size_3652_; uint8_t v_interpreted_3653_; uint8_t v_ctor_3654_; uint8_t v_hasLambdas_3655_; uint8_t v_heqProofs_3656_; lean_object* v_idx_3657_; lean_object* v_generation_3658_; lean_object* v_mt_3659_; lean_object* v_sTerms_3660_; uint8_t v_funCC_3661_; lean_object* v_ematchDiagSource_3662_; lean_object* v___x_3664_; 
v_self_3645_ = lean_ctor_get(v_rhsRoot_3427_, 0);
v_next_3646_ = lean_ctor_get(v_rhsRoot_3427_, 1);
v_root_3647_ = lean_ctor_get(v_rhsRoot_3427_, 2);
v_congr_3648_ = lean_ctor_get(v_rhsRoot_3427_, 3);
v_target_x3f_3649_ = lean_ctor_get(v_rhsRoot_3427_, 4);
v_proof_x3f_3650_ = lean_ctor_get(v_rhsRoot_3427_, 5);
v_flipped_3651_ = lean_ctor_get_uint8(v_rhsRoot_3427_, sizeof(void*)*12);
v_size_3652_ = lean_ctor_get(v_rhsRoot_3427_, 6);
v_interpreted_3653_ = lean_ctor_get_uint8(v_rhsRoot_3427_, sizeof(void*)*12 + 1);
v_ctor_3654_ = lean_ctor_get_uint8(v_rhsRoot_3427_, sizeof(void*)*12 + 2);
v_hasLambdas_3655_ = lean_ctor_get_uint8(v_rhsRoot_3427_, sizeof(void*)*12 + 3);
v_heqProofs_3656_ = lean_ctor_get_uint8(v_rhsRoot_3427_, sizeof(void*)*12 + 4);
v_idx_3657_ = lean_ctor_get(v_rhsRoot_3427_, 7);
v_generation_3658_ = lean_ctor_get(v_rhsRoot_3427_, 8);
v_mt_3659_ = lean_ctor_get(v_rhsRoot_3427_, 9);
v_sTerms_3660_ = lean_ctor_get(v_rhsRoot_3427_, 10);
v_funCC_3661_ = lean_ctor_get_uint8(v_rhsRoot_3427_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3662_ = lean_ctor_get(v_rhsRoot_3427_, 11);
lean_inc_ref(v_next_3646_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 1, v_next_3646_);
v___x_3664_ = v___x_3643_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_self_3625_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_next_3646_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_root_3626_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_congr_3627_);
lean_ctor_set(v_reuseFailAlloc_3667_, 4, v_target_x3f_3628_);
lean_ctor_set(v_reuseFailAlloc_3667_, 5, v_proof_x3f_3629_);
lean_ctor_set(v_reuseFailAlloc_3667_, 6, v_size_3631_);
lean_ctor_set(v_reuseFailAlloc_3667_, 7, v_idx_3636_);
lean_ctor_set(v_reuseFailAlloc_3667_, 8, v_generation_3637_);
lean_ctor_set(v_reuseFailAlloc_3667_, 9, v_mt_3638_);
lean_ctor_set(v_reuseFailAlloc_3667_, 10, v_sTerms_3639_);
lean_ctor_set(v_reuseFailAlloc_3667_, 11, v_ematchDiagSource_3641_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*12, v_flipped_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*12 + 1, v_interpreted_3632_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*12 + 2, v_ctor_3633_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*12 + 3, v_hasLambdas_3634_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*12 + 4, v_heqProofs_3635_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*12 + 5, v_funCC_3640_);
v___x_3664_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3600_, v___x_3664_, v___y_3608_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v___x_3666_; 
lean_dec_ref_known(v___x_3665_, 1);
v___x_3666_ = lean_nat_add(v_size_3652_, v___y_3603_);
lean_dec(v___y_3603_);
if (v_hasLambdas_3655_ == 0)
{
lean_inc(v_target_x3f_3649_);
lean_inc_ref(v_congr_3648_);
lean_inc_ref(v_root_3647_);
lean_inc(v_proof_x3f_3650_);
lean_inc(v_idx_3657_);
lean_inc(v_ematchDiagSource_3662_);
lean_inc(v_generation_3658_);
lean_inc_ref(v_self_3645_);
lean_inc(v_sTerms_3660_);
lean_inc(v_mt_3659_);
v___y_3558_ = v_mt_3659_;
v___y_3559_ = v___y_3598_;
v___y_3560_ = v___y_3608_;
v___y_3561_ = v___y_3614_;
v___y_3562_ = v_interpreted_3653_;
v___y_3563_ = v_sTerms_3660_;
v___y_3564_ = v___y_3601_;
v___y_3565_ = v___y_3602_;
v___y_3566_ = v_self_3645_;
v___y_3567_ = v_heqProofs_3656_;
v___y_3568_ = v___y_3605_;
v___y_3569_ = v___y_3611_;
v___y_3570_ = v___y_3596_;
v___y_3571_ = v___x_3621_;
v___y_3572_ = v___y_3615_;
v___y_3573_ = v___y_3613_;
v___y_3574_ = v___y_3610_;
v___y_3575_ = v___y_3606_;
v___y_3576_ = v___y_3617_;
v___y_3577_ = v_generation_3658_;
v___y_3578_ = v___x_3666_;
v___y_3579_ = v___y_3597_;
v___y_3580_ = v_ematchDiagSource_3662_;
v___y_3581_ = v___y_3609_;
v___y_3582_ = v_idx_3657_;
v___y_3583_ = v_proof_x3f_3650_;
v___y_3584_ = v_root_3647_;
v___y_3585_ = v___y_3599_;
v___y_3586_ = v_congr_3648_;
v___y_3587_ = v___y_3616_;
v___y_3588_ = v___y_3612_;
v___y_3589_ = v_flipped_3651_;
v___y_3590_ = v_funCC_3661_;
v___y_3591_ = v_target_x3f_3649_;
v___y_3592_ = v___y_3604_;
v___y_3593_ = v_ctor_3654_;
v___y_3594_ = v___y_3607_;
goto v___jp_3557_;
}
else
{
lean_inc(v_target_x3f_3649_);
lean_inc_ref(v_congr_3648_);
lean_inc_ref(v_root_3647_);
lean_inc(v_proof_x3f_3650_);
lean_inc(v_idx_3657_);
lean_inc(v_ematchDiagSource_3662_);
lean_inc(v_generation_3658_);
lean_inc_ref(v_self_3645_);
lean_inc(v_sTerms_3660_);
lean_inc(v_mt_3659_);
v___y_3558_ = v_mt_3659_;
v___y_3559_ = v___y_3598_;
v___y_3560_ = v___y_3608_;
v___y_3561_ = v___y_3614_;
v___y_3562_ = v_interpreted_3653_;
v___y_3563_ = v_sTerms_3660_;
v___y_3564_ = v___y_3601_;
v___y_3565_ = v___y_3602_;
v___y_3566_ = v_self_3645_;
v___y_3567_ = v_heqProofs_3656_;
v___y_3568_ = v___y_3605_;
v___y_3569_ = v___y_3611_;
v___y_3570_ = v___y_3596_;
v___y_3571_ = v___x_3621_;
v___y_3572_ = v___y_3615_;
v___y_3573_ = v___y_3613_;
v___y_3574_ = v___y_3610_;
v___y_3575_ = v___y_3606_;
v___y_3576_ = v___y_3617_;
v___y_3577_ = v_generation_3658_;
v___y_3578_ = v___x_3666_;
v___y_3579_ = v___y_3597_;
v___y_3580_ = v_ematchDiagSource_3662_;
v___y_3581_ = v___y_3609_;
v___y_3582_ = v_idx_3657_;
v___y_3583_ = v_proof_x3f_3650_;
v___y_3584_ = v_root_3647_;
v___y_3585_ = v___y_3599_;
v___y_3586_ = v_congr_3648_;
v___y_3587_ = v___y_3616_;
v___y_3588_ = v___y_3612_;
v___y_3589_ = v_flipped_3651_;
v___y_3590_ = v_funCC_3661_;
v___y_3591_ = v_target_x3f_3649_;
v___y_3592_ = v___y_3604_;
v___y_3593_ = v_ctor_3654_;
v___y_3594_ = v_hasLambdas_3655_;
goto v___jp_3557_;
}
}
else
{
lean_dec(v___x_3621_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v___x_3621_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
v_a_3670_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3623_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3623_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
else
{
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_lhs_3422_);
return v___x_3618_;
}
}
v___jp_3683_:
{
lean_object* v_self_3699_; lean_object* v_next_3700_; lean_object* v_size_3701_; uint8_t v_hasLambdas_3702_; uint8_t v_heqProofs_3703_; lean_object* v___x_3704_; 
v_self_3699_ = lean_ctor_get(v_lhsRoot_3426_, 0);
v_next_3700_ = lean_ctor_get(v_lhsRoot_3426_, 1);
v_size_3701_ = lean_ctor_get(v_lhsRoot_3426_, 6);
v_hasLambdas_3702_ = lean_ctor_get_uint8(v_lhsRoot_3426_, sizeof(void*)*12 + 3);
v_heqProofs_3703_ = lean_ctor_get_uint8(v_lhsRoot_3426_, sizeof(void*)*12 + 4);
v___x_3704_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3699_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v_root_3706_; lean_object* v___x_3707_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v_root_3706_ = lean_ctor_get(v_rhsNode_3425_, 2);
lean_inc_ref_n(v_root_3706_, 2);
lean_dec_ref(v_rhsNode_3425_);
lean_inc_ref(v_lhs_3422_);
v___x_3707_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3422_, v_root_3706_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_toCold_3708_; lean_object* v_options_3709_; uint8_t v_hasTrace_3710_; 
lean_dec_ref_known(v___x_3707_, 1);
v_toCold_3708_ = lean_ctor_get(v___y_3697_, 0);
v_options_3709_ = lean_ctor_get(v_toCold_3708_, 2);
v_hasTrace_3710_ = lean_ctor_get_uint8(v_options_3709_, sizeof(void*)*1);
if (v_hasTrace_3710_ == 0)
{
lean_inc(v_size_3701_);
lean_inc_ref(v_self_3699_);
lean_inc_ref(v_next_3700_);
v___y_3596_ = v_heqProofs_3703_;
v___y_3597_ = v___y_3684_;
v___y_3598_ = v_fns_u2082_3688_;
v___y_3599_ = v___y_3685_;
v___y_3600_ = v___y_3686_;
v___y_3601_ = v_next_3700_;
v___y_3602_ = v_self_3699_;
v___y_3603_ = v_size_3701_;
v___y_3604_ = v___y_3687_;
v___y_3605_ = v_root_3706_;
v___y_3606_ = v_a_3705_;
v___y_3607_ = v_hasLambdas_3702_;
v___y_3608_ = v___y_3689_;
v___y_3609_ = v___y_3690_;
v___y_3610_ = v___y_3691_;
v___y_3611_ = v___y_3692_;
v___y_3612_ = v___y_3693_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v___y_3695_;
v___y_3615_ = v___y_3696_;
v___y_3616_ = v___y_3697_;
v___y_3617_ = v___y_3698_;
goto v___jp_3595_;
}
else
{
lean_object* v_inheritedTraceOptions_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v_inheritedTraceOptions_3711_ = lean_ctor_get(v_toCold_3708_, 11);
v___x_3712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3713_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3711_, v_options_3709_, v___x_3712_);
if (v___x_3713_ == 0)
{
lean_inc(v_size_3701_);
lean_inc_ref(v_self_3699_);
lean_inc_ref(v_next_3700_);
v___y_3596_ = v_heqProofs_3703_;
v___y_3597_ = v___y_3684_;
v___y_3598_ = v_fns_u2082_3688_;
v___y_3599_ = v___y_3685_;
v___y_3600_ = v___y_3686_;
v___y_3601_ = v_next_3700_;
v___y_3602_ = v_self_3699_;
v___y_3603_ = v_size_3701_;
v___y_3604_ = v___y_3687_;
v___y_3605_ = v_root_3706_;
v___y_3606_ = v_a_3705_;
v___y_3607_ = v_hasLambdas_3702_;
v___y_3608_ = v___y_3689_;
v___y_3609_ = v___y_3690_;
v___y_3610_ = v___y_3691_;
v___y_3611_ = v___y_3692_;
v___y_3612_ = v___y_3693_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v___y_3695_;
v___y_3615_ = v___y_3696_;
v___y_3616_ = v___y_3697_;
v___y_3617_ = v___y_3698_;
goto v___jp_3595_;
}
else
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_Meta_Grind_updateLastTag(v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v___x_3715_; 
lean_dec_ref_known(v___x_3714_, 1);
lean_inc_ref(v_lhs_3422_);
v___x_3715_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3422_, v___y_3689_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
lean_inc_ref(v_root_3706_);
v___x_3717_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3706_, v___y_3689_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3719_ = lean_st_ref_get(v___y_3689_);
lean_inc_ref(v_lhs_3422_);
v___x_3720_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3719_, v_lhs_3422_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___x_3719_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3722_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
v___x_3722_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3721_, v___y_3689_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
v___x_3724_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v_a_3716_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
lean_ctor_set(v___x_3726_, 1, v_a_3718_);
v___x_3727_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
lean_ctor_set(v___x_3729_, 1, v_a_3723_);
v___x_3730_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3682_, v___x_3729_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_dec_ref_known(v___x_3730_, 1);
lean_inc(v_size_3701_);
lean_inc_ref(v_self_3699_);
lean_inc_ref(v_next_3700_);
v___y_3596_ = v_heqProofs_3703_;
v___y_3597_ = v___y_3684_;
v___y_3598_ = v_fns_u2082_3688_;
v___y_3599_ = v___y_3685_;
v___y_3600_ = v___y_3686_;
v___y_3601_ = v_next_3700_;
v___y_3602_ = v_self_3699_;
v___y_3603_ = v_size_3701_;
v___y_3604_ = v___y_3687_;
v___y_3605_ = v_root_3706_;
v___y_3606_ = v_a_3705_;
v___y_3607_ = v_hasLambdas_3702_;
v___y_3608_ = v___y_3689_;
v___y_3609_ = v___y_3690_;
v___y_3610_ = v___y_3691_;
v___y_3611_ = v___y_3692_;
v___y_3612_ = v___y_3693_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v___y_3695_;
v___y_3615_ = v___y_3696_;
v___y_3616_ = v___y_3697_;
v___y_3617_ = v___y_3698_;
goto v___jp_3595_;
}
else
{
lean_dec_ref(v_root_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_fns_u2082_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_lhs_3422_);
return v___x_3730_;
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v_a_3718_);
lean_dec(v_a_3716_);
lean_dec_ref(v_root_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_fns_u2082_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_lhs_3422_);
v_a_3731_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3722_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3722_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec(v_a_3718_);
lean_dec(v_a_3716_);
lean_dec_ref(v_root_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_fns_u2082_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_lhs_3422_);
v_a_3739_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3720_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3720_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_a_3716_);
lean_dec_ref(v_root_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_fns_u2082_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_lhs_3422_);
v_a_3747_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3717_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3717_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec_ref(v_root_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_fns_u2082_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_lhs_3422_);
v_a_3755_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3715_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3715_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
else
{
lean_dec_ref(v_root_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_fns_u2082_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_lhs_3422_);
return v___x_3714_;
}
}
}
}
else
{
lean_dec_ref(v_root_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_fns_u2082_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_lhs_3422_);
return v___x_3707_;
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec_ref(v_fns_u2082_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhs_3422_);
v_a_3763_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3704_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3704_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
v___jp_3771_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v___x_3786_ = lean_array_get_size(v___y_3774_);
v___x_3787_ = lean_unsigned_to_nat(0u);
v___x_3788_ = lean_nat_dec_eq(v___x_3786_, v___x_3787_);
if (v___x_3788_ == 0)
{
lean_object* v_self_3789_; lean_object* v___x_3790_; 
v_self_3789_ = lean_ctor_get(v_lhsRoot_3426_, 0);
lean_inc_ref(v_self_3789_);
v___x_3790_ = l_Lean_Meta_Grind_getFnRoots(v_self_3789_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
v___y_3684_ = v___y_3772_;
v___y_3685_ = v_fns_u2081_3775_;
v___y_3686_ = v___y_3773_;
v___y_3687_ = v___y_3774_;
v_fns_u2082_3688_ = v_a_3791_;
v___y_3689_ = v___y_3776_;
v___y_3690_ = v___y_3777_;
v___y_3691_ = v___y_3778_;
v___y_3692_ = v___y_3779_;
v___y_3693_ = v___y_3780_;
v___y_3694_ = v___y_3781_;
v___y_3695_ = v___y_3782_;
v___y_3696_ = v___y_3783_;
v___y_3697_ = v___y_3784_;
v___y_3698_ = v___y_3785_;
goto v___jp_3683_;
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec_ref(v_fns_u2081_3775_);
lean_dec_ref(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhs_3422_);
v_a_3792_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3790_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3790_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
lean_object* v___x_3800_; 
v___x_3800_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3684_ = v___y_3772_;
v___y_3685_ = v_fns_u2081_3775_;
v___y_3686_ = v___y_3773_;
v___y_3687_ = v___y_3774_;
v_fns_u2082_3688_ = v___x_3800_;
v___y_3689_ = v___y_3776_;
v___y_3690_ = v___y_3777_;
v___y_3691_ = v___y_3778_;
v___y_3692_ = v___y_3779_;
v___y_3693_ = v___y_3780_;
v___y_3694_ = v___y_3781_;
v___y_3695_ = v___y_3782_;
v___y_3696_ = v___y_3783_;
v___y_3697_ = v___y_3784_;
v___y_3698_ = v___y_3785_;
goto v___jp_3683_;
}
}
v___jp_3801_:
{
lean_object* v___x_3812_; 
lean_inc_ref(v_lhs_3422_);
v___x_3812_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3422_, v___y_3802_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3880_; 
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3880_ == 0)
{
lean_object* v_unused_3881_; 
v_unused_3881_ = lean_ctor_get(v___x_3812_, 0);
lean_dec(v_unused_3881_);
v___x_3814_ = v___x_3812_;
v_isShared_3815_ = v_isSharedCheck_3880_;
goto v_resetjp_3813_;
}
else
{
lean_dec(v___x_3812_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3880_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v_self_3816_; lean_object* v_next_3817_; lean_object* v_root_3818_; lean_object* v_congr_3819_; lean_object* v_size_3820_; uint8_t v_interpreted_3821_; uint8_t v_ctor_3822_; uint8_t v_hasLambdas_3823_; uint8_t v_heqProofs_3824_; lean_object* v_idx_3825_; lean_object* v_generation_3826_; lean_object* v_mt_3827_; lean_object* v_sTerms_3828_; uint8_t v_funCC_3829_; lean_object* v_ematchDiagSource_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3877_; 
v_self_3816_ = lean_ctor_get(v_lhsNode_3424_, 0);
v_next_3817_ = lean_ctor_get(v_lhsNode_3424_, 1);
v_root_3818_ = lean_ctor_get(v_lhsNode_3424_, 2);
v_congr_3819_ = lean_ctor_get(v_lhsNode_3424_, 3);
v_size_3820_ = lean_ctor_get(v_lhsNode_3424_, 6);
v_interpreted_3821_ = lean_ctor_get_uint8(v_lhsNode_3424_, sizeof(void*)*12 + 1);
v_ctor_3822_ = lean_ctor_get_uint8(v_lhsNode_3424_, sizeof(void*)*12 + 2);
v_hasLambdas_3823_ = lean_ctor_get_uint8(v_lhsNode_3424_, sizeof(void*)*12 + 3);
v_heqProofs_3824_ = lean_ctor_get_uint8(v_lhsNode_3424_, sizeof(void*)*12 + 4);
v_idx_3825_ = lean_ctor_get(v_lhsNode_3424_, 7);
v_generation_3826_ = lean_ctor_get(v_lhsNode_3424_, 8);
v_mt_3827_ = lean_ctor_get(v_lhsNode_3424_, 9);
v_sTerms_3828_ = lean_ctor_get(v_lhsNode_3424_, 10);
v_funCC_3829_ = lean_ctor_get_uint8(v_lhsNode_3424_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3830_ = lean_ctor_get(v_lhsNode_3424_, 11);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_lhsNode_3424_);
if (v_isSharedCheck_3877_ == 0)
{
lean_object* v_unused_3878_; lean_object* v_unused_3879_; 
v_unused_3878_ = lean_ctor_get(v_lhsNode_3424_, 5);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_lhsNode_3424_, 4);
lean_dec(v_unused_3879_);
v___x_3832_ = v_lhsNode_3424_;
v_isShared_3833_ = v_isSharedCheck_3877_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_ematchDiagSource_3830_);
lean_inc(v_sTerms_3828_);
lean_inc(v_mt_3827_);
lean_inc(v_generation_3826_);
lean_inc(v_idx_3825_);
lean_inc(v_size_3820_);
lean_inc(v_congr_3819_);
lean_inc(v_root_3818_);
lean_inc(v_next_3817_);
lean_inc(v_self_3816_);
lean_dec(v_lhsNode_3424_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3877_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set_tag(v___x_3814_, 1);
lean_ctor_set(v___x_3814_, 0, v_rhs_3423_);
v___x_3835_ = v___x_3814_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_rhs_3423_);
v___x_3835_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3836_, 0, v_proof_3420_);
lean_inc_ref(v_root_3818_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 5, v___x_3836_);
lean_ctor_set(v___x_3832_, 4, v___x_3835_);
v___x_3838_ = v___x_3832_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_self_3816_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_next_3817_);
lean_ctor_set(v_reuseFailAlloc_3875_, 2, v_root_3818_);
lean_ctor_set(v_reuseFailAlloc_3875_, 3, v_congr_3819_);
lean_ctor_set(v_reuseFailAlloc_3875_, 4, v___x_3835_);
lean_ctor_set(v_reuseFailAlloc_3875_, 5, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3875_, 6, v_size_3820_);
lean_ctor_set(v_reuseFailAlloc_3875_, 7, v_idx_3825_);
lean_ctor_set(v_reuseFailAlloc_3875_, 8, v_generation_3826_);
lean_ctor_set(v_reuseFailAlloc_3875_, 9, v_mt_3827_);
lean_ctor_set(v_reuseFailAlloc_3875_, 10, v_sTerms_3828_);
lean_ctor_set(v_reuseFailAlloc_3875_, 11, v_ematchDiagSource_3830_);
lean_ctor_set_uint8(v_reuseFailAlloc_3875_, sizeof(void*)*12 + 1, v_interpreted_3821_);
lean_ctor_set_uint8(v_reuseFailAlloc_3875_, sizeof(void*)*12 + 2, v_ctor_3822_);
lean_ctor_set_uint8(v_reuseFailAlloc_3875_, sizeof(void*)*12 + 3, v_hasLambdas_3823_);
lean_ctor_set_uint8(v_reuseFailAlloc_3875_, sizeof(void*)*12 + 4, v_heqProofs_3824_);
lean_ctor_set_uint8(v_reuseFailAlloc_3875_, sizeof(void*)*12 + 5, v_funCC_3829_);
v___x_3838_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3839_; 
lean_ctor_set_uint8(v___x_3838_, sizeof(void*)*12, v_flipped_3428_);
lean_inc_ref(v_lhs_3422_);
v___x_3839_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3422_, v___x_3838_, v___y_3802_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v___x_3840_; 
lean_dec_ref_known(v___x_3839_, 1);
v___x_3840_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3426_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3842_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
v___x_3842_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3427_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v___x_3842_, 1);
v___x_3844_ = lean_array_get_size(v_a_3841_);
v___x_3845_ = lean_unsigned_to_nat(0u);
v___x_3846_ = lean_nat_dec_eq(v___x_3844_, v___x_3845_);
if (v___x_3846_ == 0)
{
lean_object* v_self_3847_; lean_object* v___x_3848_; 
v_self_3847_ = lean_ctor_get(v_rhsRoot_3427_, 0);
lean_inc_ref(v_self_3847_);
v___x_3848_ = l_Lean_Meta_Grind_getFnRoots(v_self_3847_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3848_, 1);
v___y_3772_ = v_a_3841_;
v___y_3773_ = v_root_3818_;
v___y_3774_ = v_a_3843_;
v_fns_u2081_3775_ = v_a_3849_;
v___y_3776_ = v___y_3802_;
v___y_3777_ = v___y_3803_;
v___y_3778_ = v___y_3804_;
v___y_3779_ = v___y_3805_;
v___y_3780_ = v___y_3806_;
v___y_3781_ = v___y_3807_;
v___y_3782_ = v___y_3808_;
v___y_3783_ = v___y_3809_;
v___y_3784_ = v___y_3810_;
v___y_3785_ = v___y_3811_;
goto v___jp_3771_;
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec(v_a_3843_);
lean_dec(v_a_3841_);
lean_dec_ref(v_root_3818_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhs_3422_);
v_a_3850_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3848_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3848_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
else
{
lean_object* v___x_3858_; 
v___x_3858_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3772_ = v_a_3841_;
v___y_3773_ = v_root_3818_;
v___y_3774_ = v_a_3843_;
v_fns_u2081_3775_ = v___x_3858_;
v___y_3776_ = v___y_3802_;
v___y_3777_ = v___y_3803_;
v___y_3778_ = v___y_3804_;
v___y_3779_ = v___y_3805_;
v___y_3780_ = v___y_3806_;
v___y_3781_ = v___y_3807_;
v___y_3782_ = v___y_3808_;
v___y_3783_ = v___y_3809_;
v___y_3784_ = v___y_3810_;
v___y_3785_ = v___y_3811_;
goto v___jp_3771_;
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec(v_a_3841_);
lean_dec_ref(v_root_3818_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhs_3422_);
v_a_3859_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3842_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3842_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_dec_ref(v_root_3818_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhs_3422_);
v_a_3867_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3840_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3840_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
lean_dec_ref(v_root_3818_);
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhs_3422_);
return v___x_3839_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3427_);
lean_dec_ref(v_lhsRoot_3426_);
lean_dec_ref(v_rhsNode_3425_);
lean_dec_ref(v_lhsNode_3424_);
lean_dec_ref(v_rhs_3423_);
lean_dec_ref(v_lhs_3422_);
lean_dec_ref(v_proof_3420_);
return v___x_3812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3911_ = _args[0];
lean_object* v_isHEq_3912_ = _args[1];
lean_object* v_lhs_3913_ = _args[2];
lean_object* v_rhs_3914_ = _args[3];
lean_object* v_lhsNode_3915_ = _args[4];
lean_object* v_rhsNode_3916_ = _args[5];
lean_object* v_lhsRoot_3917_ = _args[6];
lean_object* v_rhsRoot_3918_ = _args[7];
lean_object* v_flipped_3919_ = _args[8];
lean_object* v_a_3920_ = _args[9];
lean_object* v_a_3921_ = _args[10];
lean_object* v_a_3922_ = _args[11];
lean_object* v_a_3923_ = _args[12];
lean_object* v_a_3924_ = _args[13];
lean_object* v_a_3925_ = _args[14];
lean_object* v_a_3926_ = _args[15];
lean_object* v_a_3927_ = _args[16];
lean_object* v_a_3928_ = _args[17];
lean_object* v_a_3929_ = _args[18];
lean_object* v_a_3930_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3931_; uint8_t v_flipped_boxed_3932_; lean_object* v_res_3933_; 
v_isHEq_boxed_3931_ = lean_unbox(v_isHEq_3912_);
v_flipped_boxed_3932_ = lean_unbox(v_flipped_3919_);
v_res_3933_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3911_, v_isHEq_boxed_3931_, v_lhs_3913_, v_rhs_3914_, v_lhsNode_3915_, v_rhsNode_3916_, v_lhsRoot_3917_, v_rhsRoot_3918_, v_flipped_boxed_3932_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
lean_dec_ref(v_a_3922_);
lean_dec(v_a_3921_);
lean_dec(v_a_3920_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3934_, lean_object* v_as_x27_3935_, lean_object* v_b_3936_, lean_object* v_a_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3935_, v_b_3936_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3950_, lean_object* v_as_x27_3951_, lean_object* v_b_3952_, lean_object* v_a_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3950_, v_as_x27_3951_, v_b_3952_, v_a_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec(v_as_x27_3951_);
lean_dec(v_as_3950_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3966_, lean_object* v_as_x27_3967_, lean_object* v_b_3968_, lean_object* v_a_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v___x_3981_; 
v___x_3981_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3967_, v_b_3968_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3982_, lean_object* v_as_x27_3983_, lean_object* v_b_3984_, lean_object* v_a_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3982_, v_as_x27_3983_, v_b_3984_, v_a_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec(v_as_x27_3983_);
lean_dec(v_as_3982_);
return v_res_3997_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4000_ = l_Lean_stringToMessageData(v___x_3999_);
return v___x_4000_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4006_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4007_ = l_Lean_Name_append(v___x_4006_, v___x_4005_);
return v___x_4007_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4010_ = l_Lean_stringToMessageData(v___x_4009_);
return v___x_4010_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4013_ = l_Lean_stringToMessageData(v___x_4012_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4014_, lean_object* v_rhs_4015_, lean_object* v_proof_4016_, uint8_t v_isHEq_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = lean_st_ref_get(v_a_4018_);
lean_inc_ref(v_lhs_4014_);
v___x_4033_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4032_, v_lhs_4014_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec(v___x_4032_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
v___x_4035_ = lean_st_ref_get(v_a_4018_);
lean_inc_ref(v_rhs_4015_);
v___x_4036_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4035_, v_rhs_4015_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec(v___x_4035_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v_root_4038_; lean_object* v_root_4039_; size_t v___x_4040_; size_t v___x_4041_; uint8_t v___x_4042_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4036_, 1);
v_root_4038_ = lean_ctor_get(v_a_4034_, 2);
v_root_4039_ = lean_ctor_get(v_a_4037_, 2);
v___x_4040_ = lean_ptr_addr(v_root_4038_);
v___x_4041_ = lean_ptr_addr(v_root_4039_);
v___x_4042_ = lean_usize_dec_eq(v___x_4040_, v___x_4041_);
if (v___x_4042_ == 0)
{
lean_object* v_toCold_4043_; lean_object* v_options_4044_; lean_object* v_inheritedTraceOptions_4045_; uint8_t v_hasTrace_4046_; uint8_t v___x_4047_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4085_; uint8_t v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4113_; uint8_t v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4143_; uint8_t v___y_4144_; uint8_t v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4159_; uint8_t v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; uint8_t v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4175_; uint8_t v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; uint8_t v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4191_; uint8_t v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; uint8_t v___y_4202_; lean_object* v___y_4203_; lean_object* v_size_4204_; uint8_t v_interpreted_4205_; uint8_t v_ctor_4206_; lean_object* v___y_4207_; lean_object* v___y_4211_; uint8_t v_ctor_4212_; uint8_t v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; uint8_t v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4233_; lean_object* v___y_4234_; uint8_t v_valueInconsistency_4235_; uint8_t v_trueEqFalse_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; uint8_t v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; 
v_toCold_4043_ = lean_ctor_get(v_a_4026_, 0);
v_options_4044_ = lean_ctor_get(v_toCold_4043_, 2);
v_inheritedTraceOptions_4045_ = lean_ctor_get(v_toCold_4043_, 11);
v_hasTrace_4046_ = lean_ctor_get_uint8(v_options_4044_, sizeof(void*)*1);
v___x_4047_ = 1;
if (v_hasTrace_4046_ == 0)
{
v___y_4293_ = v_a_4018_;
v___y_4294_ = v_a_4019_;
v___y_4295_ = v_a_4020_;
v___y_4296_ = v_a_4021_;
v___y_4297_ = v_a_4022_;
v___y_4298_ = v_a_4023_;
v___y_4299_ = v_a_4024_;
v___y_4300_ = v_a_4025_;
v___y_4301_ = v_a_4026_;
v___y_4302_ = v_a_4027_;
goto v___jp_4292_;
}
else
{
lean_object* v___x_4336_; lean_object* v_____do__lift_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4351_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4045_, v_options_4044_, v___x_4351_);
if (v___x_4352_ == 0)
{
v___y_4293_ = v_a_4018_;
v___y_4294_ = v_a_4019_;
v___y_4295_ = v_a_4020_;
v___y_4296_ = v_a_4021_;
v___y_4297_ = v_a_4022_;
v___y_4298_ = v_a_4023_;
v___y_4299_ = v_a_4024_;
v___y_4300_ = v_a_4025_;
v___y_4301_ = v_a_4026_;
v___y_4302_ = v_a_4027_;
goto v___jp_4292_;
}
else
{
lean_object* v___x_4353_; 
v___x_4353_ = l_Lean_Meta_Grind_updateLastTag(v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_dec_ref_known(v___x_4353_, 1);
if (v_isHEq_4017_ == 0)
{
lean_object* v___x_4354_; 
lean_inc_ref(v_rhs_4015_);
lean_inc_ref(v_lhs_4014_);
v___x_4354_ = l_Lean_Meta_mkEq(v_lhs_4014_, v_rhs_4015_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v_____do__lift_4338_ = v_a_4355_;
v___y_4339_ = v_a_4018_;
v___y_4340_ = v_a_4019_;
v___y_4341_ = v_a_4020_;
v___y_4342_ = v_a_4021_;
v___y_4343_ = v_a_4022_;
v___y_4344_ = v_a_4023_;
v___y_4345_ = v_a_4024_;
v___y_4346_ = v_a_4025_;
v___y_4347_ = v_a_4026_;
v___y_4348_ = v_a_4027_;
goto v___jp_4337_;
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
lean_dec(v_a_4037_);
lean_dec(v_a_4034_);
lean_dec_ref(v_proof_4016_);
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
v_a_4356_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4354_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4354_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
else
{
lean_object* v___x_4364_; 
lean_inc_ref(v_rhs_4015_);
lean_inc_ref(v_lhs_4014_);
v___x_4364_ = l_Lean_Meta_mkHEq(v_lhs_4014_, v_rhs_4015_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___x_4364_, 1);
v_____do__lift_4338_ = v_a_4365_;
v___y_4339_ = v_a_4018_;
v___y_4340_ = v_a_4019_;
v___y_4341_ = v_a_4020_;
v___y_4342_ = v_a_4021_;
v___y_4343_ = v_a_4022_;
v___y_4344_ = v_a_4023_;
v___y_4345_ = v_a_4024_;
v___y_4346_ = v_a_4025_;
v___y_4347_ = v_a_4026_;
v___y_4348_ = v_a_4027_;
goto v___jp_4337_;
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec(v_a_4037_);
lean_dec(v_a_4034_);
lean_dec_ref(v_proof_4016_);
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
v_a_4366_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4364_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4364_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
}
else
{
lean_dec(v_a_4037_);
lean_dec(v_a_4034_);
lean_dec_ref(v_proof_4016_);
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
return v___x_4353_;
}
}
v___jp_4337_:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4349_ = l_Lean_MessageData_ofExpr(v_____do__lift_4338_);
v___x_4350_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4336_, v___x_4349_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_dec_ref_known(v___x_4350_, 1);
v___y_4293_ = v___y_4339_;
v___y_4294_ = v___y_4340_;
v___y_4295_ = v___y_4341_;
v___y_4296_ = v___y_4342_;
v___y_4297_ = v___y_4343_;
v___y_4298_ = v___y_4344_;
v___y_4299_ = v___y_4345_;
v___y_4300_ = v___y_4346_;
v___y_4301_ = v___y_4347_;
v___y_4302_ = v___y_4348_;
goto v___jp_4292_;
}
else
{
lean_dec(v_a_4037_);
lean_dec(v_a_4034_);
lean_dec_ref(v_proof_4016_);
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
return v___x_4350_;
}
}
}
v___jp_4048_:
{
lean_object* v_toCold_4059_; lean_object* v_options_4060_; uint8_t v_hasTrace_4061_; 
v_toCold_4059_ = lean_ctor_get(v___y_4057_, 0);
v_options_4060_ = lean_ctor_get(v_toCold_4059_, 2);
v_hasTrace_4061_ = lean_ctor_get_uint8(v_options_4060_, sizeof(void*)*1);
if (v_hasTrace_4061_ == 0)
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Lean_Meta_Grind_checkInvariants(v___x_4042_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
return v___x_4062_;
}
else
{
lean_object* v_inheritedTraceOptions_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v_inheritedTraceOptions_4063_ = lean_ctor_get(v_toCold_4059_, 11);
v___x_4064_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4065_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4063_, v_options_4060_, v___x_4065_);
if (v___x_4066_ == 0)
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_Meta_Grind_checkInvariants(v___x_4042_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
return v___x_4067_;
}
else
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Meta_Grind_updateLastTag(v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
lean_dec_ref_known(v___x_4068_, 1);
v___x_4069_ = lean_st_ref_get(v___y_4049_);
v___x_4070_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4069_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
lean_dec(v___x_4069_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v___x_4072_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
lean_ctor_set(v___x_4073_, 1, v_a_4071_);
v___x_4074_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4064_, v___x_4073_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v___x_4075_; 
lean_dec_ref_known(v___x_4074_, 1);
v___x_4075_ = l_Lean_Meta_Grind_checkInvariants(v___x_4042_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
return v___x_4075_;
}
else
{
return v___x_4074_;
}
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
v_a_4076_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4070_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4070_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
else
{
return v___x_4068_;
}
}
}
}
v___jp_4084_:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4088_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; uint8_t v___x_4100_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4098_, 1);
v___x_4100_ = lean_unbox(v_a_4099_);
lean_dec(v_a_4099_);
if (v___x_4100_ == 0)
{
if (v___y_4086_ == 0)
{
lean_dec_ref(v___y_4087_);
lean_dec_ref(v___y_4085_);
v___y_4049_ = v___y_4088_;
v___y_4050_ = v___y_4089_;
v___y_4051_ = v___y_4090_;
v___y_4052_ = v___y_4091_;
v___y_4053_ = v___y_4092_;
v___y_4054_ = v___y_4093_;
v___y_4055_ = v___y_4094_;
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
goto v___jp_4048_;
}
else
{
lean_object* v_self_4101_; lean_object* v_self_4102_; lean_object* v___x_4103_; 
v_self_4101_ = lean_ctor_get(v___y_4085_, 0);
lean_inc_ref(v_self_4101_);
lean_dec_ref(v___y_4085_);
v_self_4102_ = lean_ctor_get(v___y_4087_, 0);
lean_inc_ref(v_self_4102_);
lean_dec_ref(v___y_4087_);
v___x_4103_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4101_, v_self_4102_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_dec_ref_known(v___x_4103_, 1);
v___y_4049_ = v___y_4088_;
v___y_4050_ = v___y_4089_;
v___y_4051_ = v___y_4090_;
v___y_4052_ = v___y_4091_;
v___y_4053_ = v___y_4092_;
v___y_4054_ = v___y_4093_;
v___y_4055_ = v___y_4094_;
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
goto v___jp_4048_;
}
else
{
return v___x_4103_;
}
}
}
else
{
lean_dec_ref(v___y_4087_);
lean_dec_ref(v___y_4085_);
v___y_4049_ = v___y_4088_;
v___y_4050_ = v___y_4089_;
v___y_4051_ = v___y_4090_;
v___y_4052_ = v___y_4091_;
v___y_4053_ = v___y_4092_;
v___y_4054_ = v___y_4093_;
v___y_4055_ = v___y_4094_;
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
goto v___jp_4048_;
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec_ref(v___y_4087_);
lean_dec_ref(v___y_4085_);
v_a_4104_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4098_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4098_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
v___jp_4112_:
{
lean_object* v___x_4126_; 
v___x_4126_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4116_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; uint8_t v___x_4128_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4126_, 1);
v___x_4128_ = lean_unbox(v_a_4127_);
lean_dec(v_a_4127_);
if (v___x_4128_ == 0)
{
uint8_t v_ctor_4129_; 
v_ctor_4129_ = lean_ctor_get_uint8(v___y_4113_, sizeof(void*)*12 + 2);
if (v_ctor_4129_ == 0)
{
v___y_4085_ = v___y_4113_;
v___y_4086_ = v___y_4114_;
v___y_4087_ = v___y_4115_;
v___y_4088_ = v___y_4116_;
v___y_4089_ = v___y_4117_;
v___y_4090_ = v___y_4118_;
v___y_4091_ = v___y_4119_;
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v___y_4094_ = v___y_4122_;
v___y_4095_ = v___y_4123_;
v___y_4096_ = v___y_4124_;
v___y_4097_ = v___y_4125_;
goto v___jp_4084_;
}
else
{
uint8_t v_ctor_4130_; 
v_ctor_4130_ = lean_ctor_get_uint8(v___y_4115_, sizeof(void*)*12 + 2);
if (v_ctor_4130_ == 0)
{
v___y_4085_ = v___y_4113_;
v___y_4086_ = v___y_4114_;
v___y_4087_ = v___y_4115_;
v___y_4088_ = v___y_4116_;
v___y_4089_ = v___y_4117_;
v___y_4090_ = v___y_4118_;
v___y_4091_ = v___y_4119_;
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v___y_4094_ = v___y_4122_;
v___y_4095_ = v___y_4123_;
v___y_4096_ = v___y_4124_;
v___y_4097_ = v___y_4125_;
goto v___jp_4084_;
}
else
{
lean_object* v_self_4131_; lean_object* v_self_4132_; lean_object* v___x_4133_; 
v_self_4131_ = lean_ctor_get(v___y_4113_, 0);
v_self_4132_ = lean_ctor_get(v___y_4115_, 0);
lean_inc_ref(v_self_4132_);
lean_inc_ref(v_self_4131_);
v___x_4133_ = l_Lean_Meta_Grind_propagateCtor(v_self_4131_, v_self_4132_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_dec_ref_known(v___x_4133_, 1);
v___y_4085_ = v___y_4113_;
v___y_4086_ = v___y_4114_;
v___y_4087_ = v___y_4115_;
v___y_4088_ = v___y_4116_;
v___y_4089_ = v___y_4117_;
v___y_4090_ = v___y_4118_;
v___y_4091_ = v___y_4119_;
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v___y_4094_ = v___y_4122_;
v___y_4095_ = v___y_4123_;
v___y_4096_ = v___y_4124_;
v___y_4097_ = v___y_4125_;
goto v___jp_4084_;
}
else
{
lean_dec_ref(v___y_4115_);
lean_dec_ref(v___y_4113_);
return v___x_4133_;
}
}
}
}
else
{
v___y_4085_ = v___y_4113_;
v___y_4086_ = v___y_4114_;
v___y_4087_ = v___y_4115_;
v___y_4088_ = v___y_4116_;
v___y_4089_ = v___y_4117_;
v___y_4090_ = v___y_4118_;
v___y_4091_ = v___y_4119_;
v___y_4092_ = v___y_4120_;
v___y_4093_ = v___y_4121_;
v___y_4094_ = v___y_4122_;
v___y_4095_ = v___y_4123_;
v___y_4096_ = v___y_4124_;
v___y_4097_ = v___y_4125_;
goto v___jp_4084_;
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec_ref(v___y_4115_);
lean_dec_ref(v___y_4113_);
v_a_4134_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4126_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4126_);
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
v___y_4113_ = v___y_4143_;
v___y_4114_ = v___y_4145_;
v___y_4115_ = v___y_4146_;
v___y_4116_ = v___y_4147_;
v___y_4117_ = v___y_4148_;
v___y_4118_ = v___y_4149_;
v___y_4119_ = v___y_4150_;
v___y_4120_ = v___y_4151_;
v___y_4121_ = v___y_4152_;
v___y_4122_ = v___y_4153_;
v___y_4123_ = v___y_4154_;
v___y_4124_ = v___y_4155_;
v___y_4125_ = v___y_4156_;
goto v___jp_4112_;
}
else
{
lean_object* v___x_4157_; 
v___x_4157_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_dec_ref_known(v___x_4157_, 1);
v___y_4113_ = v___y_4143_;
v___y_4114_ = v___y_4145_;
v___y_4115_ = v___y_4146_;
v___y_4116_ = v___y_4147_;
v___y_4117_ = v___y_4148_;
v___y_4118_ = v___y_4149_;
v___y_4119_ = v___y_4150_;
v___y_4120_ = v___y_4151_;
v___y_4121_ = v___y_4152_;
v___y_4122_ = v___y_4153_;
v___y_4123_ = v___y_4154_;
v___y_4124_ = v___y_4155_;
v___y_4125_ = v___y_4156_;
goto v___jp_4112_;
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
lean_inc_ref(v___y_4159_);
lean_inc_ref(v___y_4171_);
v___x_4173_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4016_, v_isHEq_4017_, v_rhs_4015_, v_lhs_4014_, v_a_4037_, v_a_4034_, v___y_4171_, v___y_4159_, v___x_4047_, v___y_4163_, v___y_4168_, v___y_4166_, v___y_4161_, v___y_4165_, v___y_4164_, v___y_4162_, v___y_4172_, v___y_4167_, v___y_4170_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_dec_ref_known(v___x_4173_, 1);
v___y_4143_ = v___y_4159_;
v___y_4144_ = v___y_4160_;
v___y_4145_ = v___y_4169_;
v___y_4146_ = v___y_4171_;
v___y_4147_ = v___y_4163_;
v___y_4148_ = v___y_4168_;
v___y_4149_ = v___y_4166_;
v___y_4150_ = v___y_4161_;
v___y_4151_ = v___y_4165_;
v___y_4152_ = v___y_4164_;
v___y_4153_ = v___y_4162_;
v___y_4154_ = v___y_4172_;
v___y_4155_ = v___y_4167_;
v___y_4156_ = v___y_4170_;
goto v___jp_4142_;
}
else
{
lean_dec_ref(v___y_4171_);
lean_dec_ref(v___y_4159_);
return v___x_4173_;
}
}
v___jp_4174_:
{
lean_object* v___x_4189_; 
lean_inc_ref(v___y_4187_);
lean_inc_ref(v___y_4175_);
v___x_4189_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4016_, v_isHEq_4017_, v_lhs_4014_, v_rhs_4015_, v_a_4034_, v_a_4037_, v___y_4175_, v___y_4187_, v___x_4042_, v___y_4179_, v___y_4184_, v___y_4182_, v___y_4177_, v___y_4181_, v___y_4180_, v___y_4178_, v___y_4188_, v___y_4183_, v___y_4186_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_dec_ref_known(v___x_4189_, 1);
v___y_4143_ = v___y_4175_;
v___y_4144_ = v___y_4176_;
v___y_4145_ = v___y_4185_;
v___y_4146_ = v___y_4187_;
v___y_4147_ = v___y_4179_;
v___y_4148_ = v___y_4184_;
v___y_4149_ = v___y_4182_;
v___y_4150_ = v___y_4177_;
v___y_4151_ = v___y_4181_;
v___y_4152_ = v___y_4180_;
v___y_4153_ = v___y_4178_;
v___y_4154_ = v___y_4188_;
v___y_4155_ = v___y_4183_;
v___y_4156_ = v___y_4186_;
goto v___jp_4142_;
}
else
{
lean_dec_ref(v___y_4187_);
lean_dec_ref(v___y_4175_);
return v___x_4189_;
}
}
v___jp_4190_:
{
lean_object* v_size_4208_; uint8_t v___x_4209_; 
v_size_4208_ = lean_ctor_get(v___y_4191_, 6);
v___x_4209_ = lean_nat_dec_lt(v_size_4204_, v_size_4208_);
lean_dec(v_size_4204_);
if (v___x_4209_ == 0)
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
v___y_4185_ = v___y_4202_;
v___y_4186_ = v___y_4201_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4207_;
goto v___jp_4174_;
}
else
{
if (v_interpreted_4205_ == 0)
{
if (v_ctor_4206_ == 0)
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
v___y_4169_ = v___y_4202_;
v___y_4170_ = v___y_4201_;
v___y_4171_ = v___y_4203_;
v___y_4172_ = v___y_4207_;
goto v___jp_4158_;
}
else
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
v___y_4185_ = v___y_4202_;
v___y_4186_ = v___y_4201_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4207_;
goto v___jp_4174_;
}
}
else
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
v___y_4185_ = v___y_4202_;
v___y_4186_ = v___y_4201_;
v___y_4187_ = v___y_4203_;
v___y_4188_ = v___y_4207_;
goto v___jp_4174_;
}
}
}
v___jp_4210_:
{
if (v_ctor_4212_ == 0)
{
lean_object* v_size_4226_; uint8_t v_interpreted_4227_; uint8_t v_ctor_4228_; 
v_size_4226_ = lean_ctor_get(v___y_4224_, 6);
lean_inc(v_size_4226_);
v_interpreted_4227_ = lean_ctor_get_uint8(v___y_4224_, sizeof(void*)*12 + 1);
v_ctor_4228_ = lean_ctor_get_uint8(v___y_4224_, sizeof(void*)*12 + 2);
v___y_4191_ = v___y_4211_;
v___y_4192_ = v___y_4213_;
v___y_4193_ = v___y_4214_;
v___y_4194_ = v___y_4215_;
v___y_4195_ = v___y_4216_;
v___y_4196_ = v___y_4217_;
v___y_4197_ = v___y_4218_;
v___y_4198_ = v___y_4219_;
v___y_4199_ = v___y_4220_;
v___y_4200_ = v___y_4221_;
v___y_4201_ = v___y_4222_;
v___y_4202_ = v___y_4223_;
v___y_4203_ = v___y_4224_;
v_size_4204_ = v_size_4226_;
v_interpreted_4205_ = v_interpreted_4227_;
v_ctor_4206_ = v_ctor_4228_;
v___y_4207_ = v___y_4225_;
goto v___jp_4190_;
}
else
{
uint8_t v_ctor_4229_; 
v_ctor_4229_ = lean_ctor_get_uint8(v___y_4224_, sizeof(void*)*12 + 2);
if (v_ctor_4229_ == 0)
{
v___y_4159_ = v___y_4211_;
v___y_4160_ = v___y_4213_;
v___y_4161_ = v___y_4214_;
v___y_4162_ = v___y_4215_;
v___y_4163_ = v___y_4216_;
v___y_4164_ = v___y_4217_;
v___y_4165_ = v___y_4218_;
v___y_4166_ = v___y_4219_;
v___y_4167_ = v___y_4220_;
v___y_4168_ = v___y_4221_;
v___y_4169_ = v___y_4223_;
v___y_4170_ = v___y_4222_;
v___y_4171_ = v___y_4224_;
v___y_4172_ = v___y_4225_;
goto v___jp_4158_;
}
else
{
lean_object* v_size_4230_; uint8_t v_interpreted_4231_; 
v_size_4230_ = lean_ctor_get(v___y_4224_, 6);
lean_inc(v_size_4230_);
v_interpreted_4231_ = lean_ctor_get_uint8(v___y_4224_, sizeof(void*)*12 + 1);
v___y_4191_ = v___y_4211_;
v___y_4192_ = v___y_4213_;
v___y_4193_ = v___y_4214_;
v___y_4194_ = v___y_4215_;
v___y_4195_ = v___y_4216_;
v___y_4196_ = v___y_4217_;
v___y_4197_ = v___y_4218_;
v___y_4198_ = v___y_4219_;
v___y_4199_ = v___y_4220_;
v___y_4200_ = v___y_4221_;
v___y_4201_ = v___y_4222_;
v___y_4202_ = v___y_4223_;
v___y_4203_ = v___y_4224_;
v_size_4204_ = v_size_4230_;
v_interpreted_4205_ = v_interpreted_4231_;
v_ctor_4206_ = v_ctor_4229_;
v___y_4207_ = v___y_4225_;
goto v___jp_4190_;
}
}
}
v___jp_4232_:
{
uint8_t v_interpreted_4247_; 
v_interpreted_4247_ = lean_ctor_get_uint8(v___y_4233_, sizeof(void*)*12 + 1);
if (v_interpreted_4247_ == 0)
{
uint8_t v_ctor_4248_; 
v_ctor_4248_ = lean_ctor_get_uint8(v___y_4233_, sizeof(void*)*12 + 2);
v___y_4211_ = v___y_4233_;
v_ctor_4212_ = v_ctor_4248_;
v___y_4213_ = v_trueEqFalse_4236_;
v___y_4214_ = v___y_4240_;
v___y_4215_ = v___y_4243_;
v___y_4216_ = v___y_4237_;
v___y_4217_ = v___y_4242_;
v___y_4218_ = v___y_4241_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4245_;
v___y_4221_ = v___y_4238_;
v___y_4222_ = v___y_4246_;
v___y_4223_ = v_valueInconsistency_4235_;
v___y_4224_ = v___y_4234_;
v___y_4225_ = v___y_4244_;
goto v___jp_4210_;
}
else
{
uint8_t v_interpreted_4249_; 
v_interpreted_4249_ = lean_ctor_get_uint8(v___y_4234_, sizeof(void*)*12 + 1);
if (v_interpreted_4249_ == 0)
{
v___y_4159_ = v___y_4233_;
v___y_4160_ = v_trueEqFalse_4236_;
v___y_4161_ = v___y_4240_;
v___y_4162_ = v___y_4243_;
v___y_4163_ = v___y_4237_;
v___y_4164_ = v___y_4242_;
v___y_4165_ = v___y_4241_;
v___y_4166_ = v___y_4239_;
v___y_4167_ = v___y_4245_;
v___y_4168_ = v___y_4238_;
v___y_4169_ = v_valueInconsistency_4235_;
v___y_4170_ = v___y_4246_;
v___y_4171_ = v___y_4234_;
v___y_4172_ = v___y_4244_;
goto v___jp_4158_;
}
else
{
uint8_t v_ctor_4250_; 
v_ctor_4250_ = lean_ctor_get_uint8(v___y_4233_, sizeof(void*)*12 + 2);
v___y_4211_ = v___y_4233_;
v_ctor_4212_ = v_ctor_4250_;
v___y_4213_ = v_trueEqFalse_4236_;
v___y_4214_ = v___y_4240_;
v___y_4215_ = v___y_4243_;
v___y_4216_ = v___y_4237_;
v___y_4217_ = v___y_4242_;
v___y_4218_ = v___y_4241_;
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4245_;
v___y_4221_ = v___y_4238_;
v___y_4222_ = v___y_4246_;
v___y_4223_ = v_valueInconsistency_4235_;
v___y_4224_ = v___y_4234_;
v___y_4225_ = v___y_4244_;
goto v___jp_4210_;
}
}
}
v___jp_4251_:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4261_, v___y_4256_, v___y_4252_, v___y_4254_, v___y_4259_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_dec_ref_known(v___x_4264_, 1);
v___y_4233_ = v___y_4253_;
v___y_4234_ = v___y_4262_;
v_valueInconsistency_4235_ = v___x_4042_;
v_trueEqFalse_4236_ = v___x_4047_;
v___y_4237_ = v___y_4261_;
v___y_4238_ = v___y_4260_;
v___y_4239_ = v___y_4257_;
v___y_4240_ = v___y_4255_;
v___y_4241_ = v___y_4263_;
v___y_4242_ = v___y_4258_;
v___y_4243_ = v___y_4256_;
v___y_4244_ = v___y_4252_;
v___y_4245_ = v___y_4254_;
v___y_4246_ = v___y_4259_;
goto v___jp_4232_;
}
else
{
lean_dec_ref(v___y_4262_);
lean_dec_ref(v___y_4253_);
lean_dec(v_a_4037_);
lean_dec(v_a_4034_);
lean_dec_ref(v_proof_4016_);
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
return v___x_4264_;
}
}
v___jp_4265_:
{
if (v___y_4271_ == 0)
{
lean_object* v___x_4281_; 
v___x_4281_ = l_Lean_Meta_Grind_hasSameType(v___y_4279_, v___y_4274_, v___y_4270_, v___y_4267_, v___y_4268_, v___y_4275_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_a_4282_; uint8_t v___x_4283_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v___x_4281_, 1);
v___x_4283_ = lean_unbox(v_a_4282_);
lean_dec(v_a_4282_);
if (v___x_4283_ == 0)
{
v___y_4233_ = v___y_4266_;
v___y_4234_ = v___y_4277_;
v_valueInconsistency_4235_ = v___x_4042_;
v_trueEqFalse_4236_ = v___x_4042_;
v___y_4237_ = v___y_4278_;
v___y_4238_ = v___y_4276_;
v___y_4239_ = v___y_4272_;
v___y_4240_ = v___y_4269_;
v___y_4241_ = v___y_4280_;
v___y_4242_ = v___y_4273_;
v___y_4243_ = v___y_4270_;
v___y_4244_ = v___y_4267_;
v___y_4245_ = v___y_4268_;
v___y_4246_ = v___y_4275_;
goto v___jp_4232_;
}
else
{
v___y_4233_ = v___y_4266_;
v___y_4234_ = v___y_4277_;
v_valueInconsistency_4235_ = v___x_4047_;
v_trueEqFalse_4236_ = v___x_4042_;
v___y_4237_ = v___y_4278_;
v___y_4238_ = v___y_4276_;
v___y_4239_ = v___y_4272_;
v___y_4240_ = v___y_4269_;
v___y_4241_ = v___y_4280_;
v___y_4242_ = v___y_4273_;
v___y_4243_ = v___y_4270_;
v___y_4244_ = v___y_4267_;
v___y_4245_ = v___y_4268_;
v___y_4246_ = v___y_4275_;
goto v___jp_4232_;
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_dec_ref(v___y_4277_);
lean_dec_ref(v___y_4266_);
lean_dec(v_a_4037_);
lean_dec(v_a_4034_);
lean_dec_ref(v_proof_4016_);
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
v_a_4284_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4281_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4281_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
else
{
lean_dec_ref(v___y_4279_);
lean_dec_ref(v___y_4274_);
v___y_4233_ = v___y_4266_;
v___y_4234_ = v___y_4277_;
v_valueInconsistency_4235_ = v___x_4047_;
v_trueEqFalse_4236_ = v___x_4042_;
v___y_4237_ = v___y_4278_;
v___y_4238_ = v___y_4276_;
v___y_4239_ = v___y_4272_;
v___y_4240_ = v___y_4269_;
v___y_4241_ = v___y_4280_;
v___y_4242_ = v___y_4273_;
v___y_4243_ = v___y_4270_;
v___y_4244_ = v___y_4267_;
v___y_4245_ = v___y_4268_;
v___y_4246_ = v___y_4275_;
goto v___jp_4232_;
}
}
v___jp_4292_:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4303_ = lean_st_ref_get(v___y_4293_);
lean_inc_ref(v_root_4038_);
v___x_4304_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4303_, v_root_4038_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
lean_dec(v___x_4303_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_a_4305_);
lean_dec_ref_known(v___x_4304_, 1);
v___x_4306_ = lean_st_ref_get(v___y_4293_);
lean_inc_ref(v_root_4039_);
v___x_4307_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4306_, v_root_4039_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
lean_dec(v___x_4306_);
if (lean_obj_tag(v___x_4307_) == 0)
{
uint8_t v_interpreted_4308_; 
v_interpreted_4308_ = lean_ctor_get_uint8(v_a_4305_, sizeof(void*)*12 + 1);
if (v_interpreted_4308_ == 0)
{
lean_object* v_a_4309_; uint8_t v_ctor_4310_; 
v_a_4309_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4307_, 1);
v_ctor_4310_ = lean_ctor_get_uint8(v_a_4305_, sizeof(void*)*12 + 2);
v___y_4211_ = v_a_4305_;
v_ctor_4212_ = v_ctor_4310_;
v___y_4213_ = v___x_4042_;
v___y_4214_ = v___y_4296_;
v___y_4215_ = v___y_4299_;
v___y_4216_ = v___y_4293_;
v___y_4217_ = v___y_4298_;
v___y_4218_ = v___y_4297_;
v___y_4219_ = v___y_4295_;
v___y_4220_ = v___y_4301_;
v___y_4221_ = v___y_4294_;
v___y_4222_ = v___y_4302_;
v___y_4223_ = v___x_4042_;
v___y_4224_ = v_a_4309_;
v___y_4225_ = v___y_4300_;
goto v___jp_4210_;
}
else
{
lean_object* v_a_4311_; uint8_t v_interpreted_4312_; 
v_a_4311_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4307_, 1);
v_interpreted_4312_ = lean_ctor_get_uint8(v_a_4311_, sizeof(void*)*12 + 1);
if (v_interpreted_4312_ == 0)
{
v___y_4159_ = v_a_4305_;
v___y_4160_ = v___x_4042_;
v___y_4161_ = v___y_4296_;
v___y_4162_ = v___y_4299_;
v___y_4163_ = v___y_4293_;
v___y_4164_ = v___y_4298_;
v___y_4165_ = v___y_4297_;
v___y_4166_ = v___y_4295_;
v___y_4167_ = v___y_4301_;
v___y_4168_ = v___y_4294_;
v___y_4169_ = v___x_4042_;
v___y_4170_ = v___y_4302_;
v___y_4171_ = v_a_4311_;
v___y_4172_ = v___y_4300_;
goto v___jp_4158_;
}
else
{
lean_object* v_self_4313_; uint8_t v_ctor_4314_; uint8_t v_heqProofs_4315_; lean_object* v_self_4316_; uint8_t v_heqProofs_4317_; uint8_t v___x_4318_; 
v_self_4313_ = lean_ctor_get(v_a_4305_, 0);
v_ctor_4314_ = lean_ctor_get_uint8(v_a_4305_, sizeof(void*)*12 + 2);
v_heqProofs_4315_ = lean_ctor_get_uint8(v_a_4305_, sizeof(void*)*12 + 4);
v_self_4316_ = lean_ctor_get(v_a_4311_, 0);
v_heqProofs_4317_ = lean_ctor_get_uint8(v_a_4311_, sizeof(void*)*12 + 4);
lean_inc_ref(v_root_4038_);
v___x_4318_ = l_Lean_Expr_isTrue(v_root_4038_);
if (v___x_4318_ == 0)
{
uint8_t v___x_4319_; 
lean_inc_ref(v_root_4039_);
v___x_4319_ = l_Lean_Expr_isTrue(v_root_4039_);
if (v___x_4319_ == 0)
{
if (v_isHEq_4017_ == 0)
{
if (v_heqProofs_4315_ == 0)
{
if (v_heqProofs_4317_ == 0)
{
v___y_4211_ = v_a_4305_;
v_ctor_4212_ = v_ctor_4314_;
v___y_4213_ = v___x_4042_;
v___y_4214_ = v___y_4296_;
v___y_4215_ = v___y_4299_;
v___y_4216_ = v___y_4293_;
v___y_4217_ = v___y_4298_;
v___y_4218_ = v___y_4297_;
v___y_4219_ = v___y_4295_;
v___y_4220_ = v___y_4301_;
v___y_4221_ = v___y_4294_;
v___y_4222_ = v___y_4302_;
v___y_4223_ = v___x_4047_;
v___y_4224_ = v_a_4311_;
v___y_4225_ = v___y_4300_;
goto v___jp_4210_;
}
else
{
lean_inc_ref(v_self_4316_);
lean_inc_ref(v_self_4313_);
v___y_4266_ = v_a_4305_;
v___y_4267_ = v___y_4300_;
v___y_4268_ = v___y_4301_;
v___y_4269_ = v___y_4296_;
v___y_4270_ = v___y_4299_;
v___y_4271_ = v___x_4319_;
v___y_4272_ = v___y_4295_;
v___y_4273_ = v___y_4298_;
v___y_4274_ = v_self_4316_;
v___y_4275_ = v___y_4302_;
v___y_4276_ = v___y_4294_;
v___y_4277_ = v_a_4311_;
v___y_4278_ = v___y_4293_;
v___y_4279_ = v_self_4313_;
v___y_4280_ = v___y_4297_;
goto v___jp_4265_;
}
}
else
{
lean_inc_ref(v_self_4316_);
lean_inc_ref(v_self_4313_);
v___y_4266_ = v_a_4305_;
v___y_4267_ = v___y_4300_;
v___y_4268_ = v___y_4301_;
v___y_4269_ = v___y_4296_;
v___y_4270_ = v___y_4299_;
v___y_4271_ = v___x_4319_;
v___y_4272_ = v___y_4295_;
v___y_4273_ = v___y_4298_;
v___y_4274_ = v_self_4316_;
v___y_4275_ = v___y_4302_;
v___y_4276_ = v___y_4294_;
v___y_4277_ = v_a_4311_;
v___y_4278_ = v___y_4293_;
v___y_4279_ = v_self_4313_;
v___y_4280_ = v___y_4297_;
goto v___jp_4265_;
}
}
else
{
lean_inc_ref(v_self_4316_);
lean_inc_ref(v_self_4313_);
v___y_4266_ = v_a_4305_;
v___y_4267_ = v___y_4300_;
v___y_4268_ = v___y_4301_;
v___y_4269_ = v___y_4296_;
v___y_4270_ = v___y_4299_;
v___y_4271_ = v___x_4319_;
v___y_4272_ = v___y_4295_;
v___y_4273_ = v___y_4298_;
v___y_4274_ = v_self_4316_;
v___y_4275_ = v___y_4302_;
v___y_4276_ = v___y_4294_;
v___y_4277_ = v_a_4311_;
v___y_4278_ = v___y_4293_;
v___y_4279_ = v_self_4313_;
v___y_4280_ = v___y_4297_;
goto v___jp_4265_;
}
}
else
{
v___y_4252_ = v___y_4300_;
v___y_4253_ = v_a_4305_;
v___y_4254_ = v___y_4301_;
v___y_4255_ = v___y_4296_;
v___y_4256_ = v___y_4299_;
v___y_4257_ = v___y_4295_;
v___y_4258_ = v___y_4298_;
v___y_4259_ = v___y_4302_;
v___y_4260_ = v___y_4294_;
v___y_4261_ = v___y_4293_;
v___y_4262_ = v_a_4311_;
v___y_4263_ = v___y_4297_;
goto v___jp_4251_;
}
}
else
{
v___y_4252_ = v___y_4300_;
v___y_4253_ = v_a_4305_;
v___y_4254_ = v___y_4301_;
v___y_4255_ = v___y_4296_;
v___y_4256_ = v___y_4299_;
v___y_4257_ = v___y_4295_;
v___y_4258_ = v___y_4298_;
v___y_4259_ = v___y_4302_;
v___y_4260_ = v___y_4294_;
v___y_4261_ = v___y_4293_;
v___y_4262_ = v_a_4311_;
v___y_4263_ = v___y_4297_;
goto v___jp_4251_;
}
}
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec(v_a_4305_);
lean_dec(v_a_4037_);
lean_dec(v_a_4034_);
lean_dec_ref(v_proof_4016_);
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
v_a_4320_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4307_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4307_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec(v_a_4037_);
lean_dec(v_a_4034_);
lean_dec_ref(v_proof_4016_);
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
v_a_4328_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4304_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4304_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
else
{
lean_object* v_toCold_4374_; lean_object* v_options_4375_; uint8_t v_hasTrace_4376_; 
lean_dec(v_a_4037_);
lean_dec(v_a_4034_);
lean_dec_ref(v_proof_4016_);
v_toCold_4374_ = lean_ctor_get(v_a_4026_, 0);
v_options_4375_ = lean_ctor_get(v_toCold_4374_, 2);
v_hasTrace_4376_ = lean_ctor_get_uint8(v_options_4375_, sizeof(void*)*1);
if (v_hasTrace_4376_ == 0)
{
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
goto v___jp_4029_;
}
else
{
lean_object* v_inheritedTraceOptions_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; uint8_t v___x_4380_; 
v_inheritedTraceOptions_4377_ = lean_ctor_get(v_toCold_4374_, 11);
v___x_4378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4379_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4380_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4377_, v_options_4375_, v___x_4379_);
if (v___x_4380_ == 0)
{
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
goto v___jp_4029_;
}
else
{
lean_object* v___x_4381_; 
v___x_4381_ = l_Lean_Meta_Grind_updateLastTag(v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v___x_4382_; 
lean_dec_ref_known(v___x_4381_, 1);
v___x_4382_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4014_, v_a_4018_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4384_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v___x_4382_, 1);
v___x_4384_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4015_, v_a_4018_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v_a_4383_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
lean_ctor_set(v___x_4388_, 1, v_a_4385_);
v___x_4389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4388_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
v___x_4391_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4378_, v___x_4390_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_dec_ref_known(v___x_4391_, 1);
goto v___jp_4029_;
}
else
{
return v___x_4391_;
}
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
lean_dec(v_a_4383_);
v_a_4392_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4384_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4384_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec_ref(v_rhs_4015_);
v_a_4400_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4382_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4382_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
return v___x_4381_;
}
}
}
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec(v_a_4034_);
lean_dec_ref(v_proof_4016_);
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
v_a_4408_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4036_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4036_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_dec_ref(v_proof_4016_);
lean_dec_ref(v_rhs_4015_);
lean_dec_ref(v_lhs_4014_);
v_a_4416_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4033_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4033_);
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
v___jp_4029_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = lean_box(0);
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
return v___x_4031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4424_, lean_object* v_rhs_4425_, lean_object* v_proof_4426_, lean_object* v_isHEq_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_){
_start:
{
uint8_t v_isHEq_boxed_4439_; lean_object* v_res_4440_; 
v_isHEq_boxed_4439_ = lean_unbox(v_isHEq_4427_);
v_res_4440_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4424_, v_rhs_4425_, v_proof_4426_, v_isHEq_boxed_4439_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_);
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
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4443_){
_start:
{
lean_object* v___x_4445_; lean_object* v_toGoalState_4446_; lean_object* v_mvarId_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4483_; 
v___x_4445_ = lean_st_ref_take(v_a_4443_);
v_toGoalState_4446_ = lean_ctor_get(v___x_4445_, 0);
v_mvarId_4447_ = lean_ctor_get(v___x_4445_, 1);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4449_ = v___x_4445_;
v_isShared_4450_ = v_isSharedCheck_4483_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_mvarId_4447_);
lean_inc(v_toGoalState_4446_);
lean_dec(v___x_4445_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4483_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v_nextDeclIdx_4451_; lean_object* v_enodeMap_4452_; lean_object* v_exprs_4453_; lean_object* v_parents_4454_; lean_object* v_congrTable_4455_; lean_object* v_appMap_4456_; lean_object* v_indicesFound_4457_; uint8_t v_inconsistent_4458_; lean_object* v_nextIdx_4459_; lean_object* v_newRawFacts_4460_; lean_object* v_facts_4461_; lean_object* v_extThms_4462_; lean_object* v_ematch_4463_; lean_object* v_inj_4464_; lean_object* v_split_4465_; lean_object* v_clean_4466_; lean_object* v_sstates_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4481_; 
v_nextDeclIdx_4451_ = lean_ctor_get(v_toGoalState_4446_, 0);
v_enodeMap_4452_ = lean_ctor_get(v_toGoalState_4446_, 1);
v_exprs_4453_ = lean_ctor_get(v_toGoalState_4446_, 2);
v_parents_4454_ = lean_ctor_get(v_toGoalState_4446_, 3);
v_congrTable_4455_ = lean_ctor_get(v_toGoalState_4446_, 4);
v_appMap_4456_ = lean_ctor_get(v_toGoalState_4446_, 5);
v_indicesFound_4457_ = lean_ctor_get(v_toGoalState_4446_, 6);
v_inconsistent_4458_ = lean_ctor_get_uint8(v_toGoalState_4446_, sizeof(void*)*17);
v_nextIdx_4459_ = lean_ctor_get(v_toGoalState_4446_, 8);
v_newRawFacts_4460_ = lean_ctor_get(v_toGoalState_4446_, 9);
v_facts_4461_ = lean_ctor_get(v_toGoalState_4446_, 10);
v_extThms_4462_ = lean_ctor_get(v_toGoalState_4446_, 11);
v_ematch_4463_ = lean_ctor_get(v_toGoalState_4446_, 12);
v_inj_4464_ = lean_ctor_get(v_toGoalState_4446_, 13);
v_split_4465_ = lean_ctor_get(v_toGoalState_4446_, 14);
v_clean_4466_ = lean_ctor_get(v_toGoalState_4446_, 15);
v_sstates_4467_ = lean_ctor_get(v_toGoalState_4446_, 16);
v_isSharedCheck_4481_ = !lean_is_exclusive(v_toGoalState_4446_);
if (v_isSharedCheck_4481_ == 0)
{
lean_object* v_unused_4482_; 
v_unused_4482_ = lean_ctor_get(v_toGoalState_4446_, 7);
lean_dec(v_unused_4482_);
v___x_4469_ = v_toGoalState_4446_;
v_isShared_4470_ = v_isSharedCheck_4481_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_sstates_4467_);
lean_inc(v_clean_4466_);
lean_inc(v_split_4465_);
lean_inc(v_inj_4464_);
lean_inc(v_ematch_4463_);
lean_inc(v_extThms_4462_);
lean_inc(v_facts_4461_);
lean_inc(v_newRawFacts_4460_);
lean_inc(v_nextIdx_4459_);
lean_inc(v_indicesFound_4457_);
lean_inc(v_appMap_4456_);
lean_inc(v_congrTable_4455_);
lean_inc(v_parents_4454_);
lean_inc(v_exprs_4453_);
lean_inc(v_enodeMap_4452_);
lean_inc(v_nextDeclIdx_4451_);
lean_dec(v_toGoalState_4446_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4481_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4474_; 
v___x_4471_ = lean_box(0);
v___x_4472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 7, v___x_4472_);
v___x_4474_ = v___x_4469_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_nextDeclIdx_4451_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_enodeMap_4452_);
lean_ctor_set(v_reuseFailAlloc_4480_, 2, v_exprs_4453_);
lean_ctor_set(v_reuseFailAlloc_4480_, 3, v_parents_4454_);
lean_ctor_set(v_reuseFailAlloc_4480_, 4, v_congrTable_4455_);
lean_ctor_set(v_reuseFailAlloc_4480_, 5, v_appMap_4456_);
lean_ctor_set(v_reuseFailAlloc_4480_, 6, v_indicesFound_4457_);
lean_ctor_set(v_reuseFailAlloc_4480_, 7, v___x_4472_);
lean_ctor_set(v_reuseFailAlloc_4480_, 8, v_nextIdx_4459_);
lean_ctor_set(v_reuseFailAlloc_4480_, 9, v_newRawFacts_4460_);
lean_ctor_set(v_reuseFailAlloc_4480_, 10, v_facts_4461_);
lean_ctor_set(v_reuseFailAlloc_4480_, 11, v_extThms_4462_);
lean_ctor_set(v_reuseFailAlloc_4480_, 12, v_ematch_4463_);
lean_ctor_set(v_reuseFailAlloc_4480_, 13, v_inj_4464_);
lean_ctor_set(v_reuseFailAlloc_4480_, 14, v_split_4465_);
lean_ctor_set(v_reuseFailAlloc_4480_, 15, v_clean_4466_);
lean_ctor_set(v_reuseFailAlloc_4480_, 16, v_sstates_4467_);
lean_ctor_set_uint8(v_reuseFailAlloc_4480_, sizeof(void*)*17, v_inconsistent_4458_);
v___x_4474_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
lean_object* v___x_4476_; 
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4474_);
v___x_4476_ = v___x_4449_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4474_);
lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_mvarId_4447_);
v___x_4476_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4477_ = lean_st_ref_put(v_a_4443_, v___x_4476_);
v___x_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4471_);
return v___x_4478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4484_);
lean_dec(v_a_4484_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4487_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec(v_a_4499_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4511_){
_start:
{
lean_object* v___x_4513_; lean_object* v_toGoalState_4514_; lean_object* v_newFacts_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4513_ = lean_st_ref_get(v_a_4511_);
v_toGoalState_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc_ref(v_toGoalState_4514_);
lean_dec(v___x_4513_);
v_newFacts_4515_ = lean_ctor_get(v_toGoalState_4514_, 7);
lean_inc_ref(v_newFacts_4515_);
lean_dec_ref(v_toGoalState_4514_);
v___x_4516_ = lean_array_get_size(v_newFacts_4515_);
v___x_4517_ = lean_unsigned_to_nat(1u);
v___x_4518_ = lean_nat_sub(v___x_4516_, v___x_4517_);
v___x_4519_ = lean_nat_dec_lt(v___x_4518_, v___x_4516_);
if (v___x_4519_ == 0)
{
lean_object* v___x_4520_; lean_object* v___x_4521_; 
lean_dec(v___x_4518_);
lean_dec_ref(v_newFacts_4515_);
v___x_4520_ = lean_box(0);
v___x_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4520_);
return v___x_4521_;
}
else
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v_toGoalState_4525_; lean_object* v_mvarId_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4561_; 
v___x_4522_ = lean_array_fget(v_newFacts_4515_, v___x_4518_);
lean_dec(v___x_4518_);
lean_dec_ref(v_newFacts_4515_);
v___x_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
v___x_4524_ = lean_st_ref_take(v_a_4511_);
v_toGoalState_4525_ = lean_ctor_get(v___x_4524_, 0);
v_mvarId_4526_ = lean_ctor_get(v___x_4524_, 1);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4528_ = v___x_4524_;
v_isShared_4529_ = v_isSharedCheck_4561_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_mvarId_4526_);
lean_inc(v_toGoalState_4525_);
lean_dec(v___x_4524_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4561_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v_nextDeclIdx_4530_; lean_object* v_enodeMap_4531_; lean_object* v_exprs_4532_; lean_object* v_parents_4533_; lean_object* v_congrTable_4534_; lean_object* v_appMap_4535_; lean_object* v_indicesFound_4536_; lean_object* v_newFacts_4537_; uint8_t v_inconsistent_4538_; lean_object* v_nextIdx_4539_; lean_object* v_newRawFacts_4540_; lean_object* v_facts_4541_; lean_object* v_extThms_4542_; lean_object* v_ematch_4543_; lean_object* v_inj_4544_; lean_object* v_split_4545_; lean_object* v_clean_4546_; lean_object* v_sstates_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4560_; 
v_nextDeclIdx_4530_ = lean_ctor_get(v_toGoalState_4525_, 0);
v_enodeMap_4531_ = lean_ctor_get(v_toGoalState_4525_, 1);
v_exprs_4532_ = lean_ctor_get(v_toGoalState_4525_, 2);
v_parents_4533_ = lean_ctor_get(v_toGoalState_4525_, 3);
v_congrTable_4534_ = lean_ctor_get(v_toGoalState_4525_, 4);
v_appMap_4535_ = lean_ctor_get(v_toGoalState_4525_, 5);
v_indicesFound_4536_ = lean_ctor_get(v_toGoalState_4525_, 6);
v_newFacts_4537_ = lean_ctor_get(v_toGoalState_4525_, 7);
v_inconsistent_4538_ = lean_ctor_get_uint8(v_toGoalState_4525_, sizeof(void*)*17);
v_nextIdx_4539_ = lean_ctor_get(v_toGoalState_4525_, 8);
v_newRawFacts_4540_ = lean_ctor_get(v_toGoalState_4525_, 9);
v_facts_4541_ = lean_ctor_get(v_toGoalState_4525_, 10);
v_extThms_4542_ = lean_ctor_get(v_toGoalState_4525_, 11);
v_ematch_4543_ = lean_ctor_get(v_toGoalState_4525_, 12);
v_inj_4544_ = lean_ctor_get(v_toGoalState_4525_, 13);
v_split_4545_ = lean_ctor_get(v_toGoalState_4525_, 14);
v_clean_4546_ = lean_ctor_get(v_toGoalState_4525_, 15);
v_sstates_4547_ = lean_ctor_get(v_toGoalState_4525_, 16);
v_isSharedCheck_4560_ = !lean_is_exclusive(v_toGoalState_4525_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4549_ = v_toGoalState_4525_;
v_isShared_4550_ = v_isSharedCheck_4560_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_sstates_4547_);
lean_inc(v_clean_4546_);
lean_inc(v_split_4545_);
lean_inc(v_inj_4544_);
lean_inc(v_ematch_4543_);
lean_inc(v_extThms_4542_);
lean_inc(v_facts_4541_);
lean_inc(v_newRawFacts_4540_);
lean_inc(v_nextIdx_4539_);
lean_inc(v_newFacts_4537_);
lean_inc(v_indicesFound_4536_);
lean_inc(v_appMap_4535_);
lean_inc(v_congrTable_4534_);
lean_inc(v_parents_4533_);
lean_inc(v_exprs_4532_);
lean_inc(v_enodeMap_4531_);
lean_inc(v_nextDeclIdx_4530_);
lean_dec(v_toGoalState_4525_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4560_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4551_; lean_object* v___x_4553_; 
v___x_4551_ = lean_array_pop(v_newFacts_4537_);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 7, v___x_4551_);
v___x_4553_ = v___x_4549_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_nextDeclIdx_4530_);
lean_ctor_set(v_reuseFailAlloc_4559_, 1, v_enodeMap_4531_);
lean_ctor_set(v_reuseFailAlloc_4559_, 2, v_exprs_4532_);
lean_ctor_set(v_reuseFailAlloc_4559_, 3, v_parents_4533_);
lean_ctor_set(v_reuseFailAlloc_4559_, 4, v_congrTable_4534_);
lean_ctor_set(v_reuseFailAlloc_4559_, 5, v_appMap_4535_);
lean_ctor_set(v_reuseFailAlloc_4559_, 6, v_indicesFound_4536_);
lean_ctor_set(v_reuseFailAlloc_4559_, 7, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4559_, 8, v_nextIdx_4539_);
lean_ctor_set(v_reuseFailAlloc_4559_, 9, v_newRawFacts_4540_);
lean_ctor_set(v_reuseFailAlloc_4559_, 10, v_facts_4541_);
lean_ctor_set(v_reuseFailAlloc_4559_, 11, v_extThms_4542_);
lean_ctor_set(v_reuseFailAlloc_4559_, 12, v_ematch_4543_);
lean_ctor_set(v_reuseFailAlloc_4559_, 13, v_inj_4544_);
lean_ctor_set(v_reuseFailAlloc_4559_, 14, v_split_4545_);
lean_ctor_set(v_reuseFailAlloc_4559_, 15, v_clean_4546_);
lean_ctor_set(v_reuseFailAlloc_4559_, 16, v_sstates_4547_);
lean_ctor_set_uint8(v_reuseFailAlloc_4559_, sizeof(void*)*17, v_inconsistent_4538_);
v___x_4553_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4555_; 
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 0, v___x_4553_);
v___x_4555_ = v___x_4528_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4553_);
lean_ctor_set(v_reuseFailAlloc_4558_, 1, v_mvarId_4526_);
v___x_4555_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4556_ = lean_st_ref_put(v_a_4511_, v___x_4555_);
v___x_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4523_);
return v___x_4557_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4562_, lean_object* v_a_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4562_);
lean_dec(v_a_4562_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_){
_start:
{
lean_object* v___x_4576_; 
v___x_4576_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4565_);
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_);
lean_dec(v_a_4586_);
lean_dec_ref(v_a_4585_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
lean_dec(v_a_4582_);
lean_dec_ref(v_a_4581_);
lean_dec(v_a_4580_);
lean_dec_ref(v_a_4579_);
lean_dec(v_a_4578_);
lean_dec(v_a_4577_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4589_, lean_object* v_rhs_4590_, lean_object* v_proof_4591_, uint8_t v_isHEq_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4589_, v_rhs_4590_, v_proof_4591_, v_isHEq_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v___x_4605_; 
lean_dec_ref_known(v___x_4604_, 1);
lean_inc(v_a_4602_);
lean_inc_ref(v_a_4601_);
lean_inc(v_a_4600_);
lean_inc_ref(v_a_4599_);
lean_inc(v_a_4598_);
lean_inc_ref(v_a_4597_);
lean_inc(v_a_4596_);
lean_inc_ref(v_a_4595_);
lean_inc(v_a_4594_);
lean_inc(v_a_4593_);
v___x_4605_ = lean_grind_process_new_facts(v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
return v___x_4605_;
}
else
{
return v___x_4604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4606_, lean_object* v_rhs_4607_, lean_object* v_proof_4608_, lean_object* v_isHEq_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_){
_start:
{
uint8_t v_isHEq_boxed_4621_; lean_object* v_res_4622_; 
v_isHEq_boxed_4621_ = lean_unbox(v_isHEq_4609_);
v_res_4622_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4606_, v_rhs_4607_, v_proof_4608_, v_isHEq_boxed_4621_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_);
lean_dec(v_a_4619_);
lean_dec_ref(v_a_4618_);
lean_dec(v_a_4617_);
lean_dec_ref(v_a_4616_);
lean_dec(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec(v_a_4613_);
lean_dec_ref(v_a_4612_);
lean_dec(v_a_4611_);
lean_dec(v_a_4610_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4623_, lean_object* v_rhs_4624_, lean_object* v_proof_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
uint8_t v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = 0;
v___x_4638_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4623_, v_rhs_4624_, v_proof_4625_, v___x_4637_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4639_, lean_object* v_rhs_4640_, lean_object* v_proof_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4639_, v_rhs_4640_, v_proof_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
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
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4654_, lean_object* v_rhs_4655_, lean_object* v_proof_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
uint8_t v___x_4668_; lean_object* v___x_4669_; 
v___x_4668_ = 1;
v___x_4669_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4654_, v_rhs_4655_, v_proof_4656_, v___x_4668_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
return v___x_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4670_, lean_object* v_rhs_4671_, lean_object* v_proof_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4670_, v_rhs_4671_, v_proof_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v___x_4688_; lean_object* v_toGoalState_4689_; lean_object* v_mvarId_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4726_; 
v___x_4688_ = lean_st_ref_take(v_a_4686_);
v_toGoalState_4689_ = lean_ctor_get(v___x_4688_, 0);
v_mvarId_4690_ = lean_ctor_get(v___x_4688_, 1);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4692_ = v___x_4688_;
v_isShared_4693_ = v_isSharedCheck_4726_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_mvarId_4690_);
lean_inc(v_toGoalState_4689_);
lean_dec(v___x_4688_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4726_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v_nextDeclIdx_4694_; lean_object* v_enodeMap_4695_; lean_object* v_exprs_4696_; lean_object* v_parents_4697_; lean_object* v_congrTable_4698_; lean_object* v_appMap_4699_; lean_object* v_indicesFound_4700_; lean_object* v_newFacts_4701_; uint8_t v_inconsistent_4702_; lean_object* v_nextIdx_4703_; lean_object* v_newRawFacts_4704_; lean_object* v_facts_4705_; lean_object* v_extThms_4706_; lean_object* v_ematch_4707_; lean_object* v_inj_4708_; lean_object* v_split_4709_; lean_object* v_clean_4710_; lean_object* v_sstates_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4725_; 
v_nextDeclIdx_4694_ = lean_ctor_get(v_toGoalState_4689_, 0);
v_enodeMap_4695_ = lean_ctor_get(v_toGoalState_4689_, 1);
v_exprs_4696_ = lean_ctor_get(v_toGoalState_4689_, 2);
v_parents_4697_ = lean_ctor_get(v_toGoalState_4689_, 3);
v_congrTable_4698_ = lean_ctor_get(v_toGoalState_4689_, 4);
v_appMap_4699_ = lean_ctor_get(v_toGoalState_4689_, 5);
v_indicesFound_4700_ = lean_ctor_get(v_toGoalState_4689_, 6);
v_newFacts_4701_ = lean_ctor_get(v_toGoalState_4689_, 7);
v_inconsistent_4702_ = lean_ctor_get_uint8(v_toGoalState_4689_, sizeof(void*)*17);
v_nextIdx_4703_ = lean_ctor_get(v_toGoalState_4689_, 8);
v_newRawFacts_4704_ = lean_ctor_get(v_toGoalState_4689_, 9);
v_facts_4705_ = lean_ctor_get(v_toGoalState_4689_, 10);
v_extThms_4706_ = lean_ctor_get(v_toGoalState_4689_, 11);
v_ematch_4707_ = lean_ctor_get(v_toGoalState_4689_, 12);
v_inj_4708_ = lean_ctor_get(v_toGoalState_4689_, 13);
v_split_4709_ = lean_ctor_get(v_toGoalState_4689_, 14);
v_clean_4710_ = lean_ctor_get(v_toGoalState_4689_, 15);
v_sstates_4711_ = lean_ctor_get(v_toGoalState_4689_, 16);
v_isSharedCheck_4725_ = !lean_is_exclusive(v_toGoalState_4689_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4713_ = v_toGoalState_4689_;
v_isShared_4714_ = v_isSharedCheck_4725_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_sstates_4711_);
lean_inc(v_clean_4710_);
lean_inc(v_split_4709_);
lean_inc(v_inj_4708_);
lean_inc(v_ematch_4707_);
lean_inc(v_extThms_4706_);
lean_inc(v_facts_4705_);
lean_inc(v_newRawFacts_4704_);
lean_inc(v_nextIdx_4703_);
lean_inc(v_newFacts_4701_);
lean_inc(v_indicesFound_4700_);
lean_inc(v_appMap_4699_);
lean_inc(v_congrTable_4698_);
lean_inc(v_parents_4697_);
lean_inc(v_exprs_4696_);
lean_inc(v_enodeMap_4695_);
lean_inc(v_nextDeclIdx_4694_);
lean_dec(v_toGoalState_4689_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4725_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4718_; 
v___x_4715_ = lean_box(0);
v___x_4716_ = l_Lean_PersistentArray_push___redArg(v_facts_4705_, v_fact_4685_);
if (v_isShared_4714_ == 0)
{
lean_ctor_set(v___x_4713_, 10, v___x_4716_);
v___x_4718_ = v___x_4713_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_nextDeclIdx_4694_);
lean_ctor_set(v_reuseFailAlloc_4724_, 1, v_enodeMap_4695_);
lean_ctor_set(v_reuseFailAlloc_4724_, 2, v_exprs_4696_);
lean_ctor_set(v_reuseFailAlloc_4724_, 3, v_parents_4697_);
lean_ctor_set(v_reuseFailAlloc_4724_, 4, v_congrTable_4698_);
lean_ctor_set(v_reuseFailAlloc_4724_, 5, v_appMap_4699_);
lean_ctor_set(v_reuseFailAlloc_4724_, 6, v_indicesFound_4700_);
lean_ctor_set(v_reuseFailAlloc_4724_, 7, v_newFacts_4701_);
lean_ctor_set(v_reuseFailAlloc_4724_, 8, v_nextIdx_4703_);
lean_ctor_set(v_reuseFailAlloc_4724_, 9, v_newRawFacts_4704_);
lean_ctor_set(v_reuseFailAlloc_4724_, 10, v___x_4716_);
lean_ctor_set(v_reuseFailAlloc_4724_, 11, v_extThms_4706_);
lean_ctor_set(v_reuseFailAlloc_4724_, 12, v_ematch_4707_);
lean_ctor_set(v_reuseFailAlloc_4724_, 13, v_inj_4708_);
lean_ctor_set(v_reuseFailAlloc_4724_, 14, v_split_4709_);
lean_ctor_set(v_reuseFailAlloc_4724_, 15, v_clean_4710_);
lean_ctor_set(v_reuseFailAlloc_4724_, 16, v_sstates_4711_);
lean_ctor_set_uint8(v_reuseFailAlloc_4724_, sizeof(void*)*17, v_inconsistent_4702_);
v___x_4718_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
lean_object* v___x_4720_; 
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 0, v___x_4718_);
v___x_4720_ = v___x_4692_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4718_);
lean_ctor_set(v_reuseFailAlloc_4723_, 1, v_mvarId_4690_);
v___x_4720_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4721_ = lean_st_ref_put(v_a_4686_, v___x_4720_);
v___x_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4715_);
return v___x_4722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4727_, v_a_4728_);
lean_dec(v_a_4728_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v___x_4743_; 
v___x_4743_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4731_, v_a_4732_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_){
_start:
{
lean_object* v_res_4756_; 
v_res_4756_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
lean_dec(v_a_4748_);
lean_dec_ref(v_a_4747_);
lean_dec(v_a_4746_);
lean_dec(v_a_4745_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4757_, lean_object* v_rhs_4758_, lean_object* v_proof_4759_, lean_object* v_generation_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v___x_4772_; 
lean_inc_ref(v_rhs_4758_);
lean_inc_ref(v_lhs_4757_);
v___x_4772_ = l_Lean_Meta_mkEq(v_lhs_4757_, v_rhs_4758_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
if (lean_obj_tag(v___x_4772_) == 0)
{
lean_object* v_a_4773_; lean_object* v___x_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4784_; 
v_a_4773_ = lean_ctor_get(v___x_4772_, 0);
lean_inc_n(v_a_4773_, 2);
lean_dec_ref_known(v___x_4772_, 1);
v___x_4774_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4773_, v_a_4761_);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4784_ == 0)
{
lean_object* v_unused_4785_; 
v_unused_4785_ = lean_ctor_get(v___x_4774_, 0);
lean_dec(v_unused_4785_);
v___x_4776_ = v___x_4774_;
v_isShared_4777_ = v_isSharedCheck_4784_;
goto v_resetjp_4775_;
}
else
{
lean_dec(v___x_4774_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4784_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
lean_ctor_set_tag(v___x_4776_, 1);
lean_ctor_set(v___x_4776_, 0, v_a_4773_);
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4773_);
v___x_4779_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
lean_object* v___x_4780_; 
lean_inc(v_a_4770_);
lean_inc_ref(v_a_4769_);
lean_inc(v_a_4768_);
lean_inc_ref(v_a_4767_);
lean_inc(v_a_4766_);
lean_inc_ref(v_a_4765_);
lean_inc(v_a_4764_);
lean_inc_ref(v_a_4763_);
lean_inc(v_a_4762_);
lean_inc(v_a_4761_);
lean_inc_ref(v___x_4779_);
lean_inc(v_generation_4760_);
lean_inc_ref(v_lhs_4757_);
v___x_4780_ = lean_grind_internalize(v_lhs_4757_, v_generation_4760_, v___x_4779_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v___x_4781_; 
lean_dec_ref_known(v___x_4780_, 1);
lean_inc(v_a_4770_);
lean_inc_ref(v_a_4769_);
lean_inc(v_a_4768_);
lean_inc_ref(v_a_4767_);
lean_inc(v_a_4766_);
lean_inc_ref(v_a_4765_);
lean_inc(v_a_4764_);
lean_inc_ref(v_a_4763_);
lean_inc(v_a_4762_);
lean_inc(v_a_4761_);
lean_inc_ref(v_rhs_4758_);
v___x_4781_ = lean_grind_internalize(v_rhs_4758_, v_generation_4760_, v___x_4779_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v___x_4782_; 
lean_dec_ref_known(v___x_4781_, 1);
v___x_4782_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4757_, v_rhs_4758_, v_proof_4759_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
return v___x_4782_;
}
else
{
lean_dec_ref(v_proof_4759_);
lean_dec_ref(v_rhs_4758_);
lean_dec_ref(v_lhs_4757_);
return v___x_4781_;
}
}
else
{
lean_dec_ref(v___x_4779_);
lean_dec(v_generation_4760_);
lean_dec_ref(v_proof_4759_);
lean_dec_ref(v_rhs_4758_);
lean_dec_ref(v_lhs_4757_);
return v___x_4780_;
}
}
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec(v_generation_4760_);
lean_dec_ref(v_proof_4759_);
lean_dec_ref(v_rhs_4758_);
lean_dec_ref(v_lhs_4757_);
v_a_4786_ = lean_ctor_get(v___x_4772_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4772_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4772_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4772_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4794_, lean_object* v_rhs_4795_, lean_object* v_proof_4796_, lean_object* v_generation_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4794_, v_rhs_4795_, v_proof_4796_, v_generation_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec_ref(v_a_4802_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
lean_dec(v_a_4799_);
lean_dec(v_a_4798_);
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4810_, lean_object* v_generation_4811_, lean_object* v_p_4812_, uint8_t v_isNeg_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_){
_start:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4825_ = lean_box(0);
lean_inc(v_a_4823_);
lean_inc_ref(v_a_4822_);
lean_inc(v_a_4821_);
lean_inc_ref(v_a_4820_);
lean_inc(v_a_4819_);
lean_inc_ref(v_a_4818_);
lean_inc(v_a_4817_);
lean_inc_ref(v_a_4816_);
lean_inc(v_a_4815_);
lean_inc(v_a_4814_);
lean_inc_ref(v_p_4812_);
v___x_4826_ = lean_grind_internalize(v_p_4812_, v_generation_4811_, v___x_4825_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_dec_ref_known(v___x_4826_, 1);
if (v_isNeg_4813_ == 0)
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4818_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; lean_object* v___x_4829_; 
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_a_4828_);
lean_dec_ref_known(v___x_4827_, 1);
v___x_4829_ = l_Lean_Meta_mkEqTrue(v_proof_4810_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v_a_4830_; lean_object* v___x_4831_; 
v_a_4830_ = lean_ctor_get(v___x_4829_, 0);
lean_inc(v_a_4830_);
lean_dec_ref_known(v___x_4829_, 1);
v___x_4831_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4812_, v_a_4828_, v_a_4830_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
return v___x_4831_;
}
else
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4839_; 
lean_dec(v_a_4828_);
lean_dec_ref(v_p_4812_);
v_a_4832_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4834_ = v___x_4829_;
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4829_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4837_; 
if (v_isShared_4835_ == 0)
{
v___x_4837_ = v___x_4834_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
}
}
else
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4847_; 
lean_dec_ref(v_p_4812_);
lean_dec_ref(v_proof_4810_);
v_a_4840_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4827_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4827_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4845_; 
if (v_isShared_4843_ == 0)
{
v___x_4845_ = v___x_4842_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_a_4840_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
else
{
lean_object* v___x_4848_; 
v___x_4848_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4818_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v___x_4850_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_a_4849_);
lean_dec_ref_known(v___x_4848_, 1);
v___x_4850_ = l_Lean_Meta_mkEqFalse(v_proof_4810_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4852_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_a_4851_);
lean_dec_ref_known(v___x_4850_, 1);
v___x_4852_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4812_, v_a_4849_, v_a_4851_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
return v___x_4852_;
}
else
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4860_; 
lean_dec(v_a_4849_);
lean_dec_ref(v_p_4812_);
v_a_4853_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4855_ = v___x_4850_;
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4850_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4860_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
lean_object* v___x_4858_; 
if (v_isShared_4856_ == 0)
{
v___x_4858_ = v___x_4855_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
lean_dec_ref(v_p_4812_);
lean_dec_ref(v_proof_4810_);
v_a_4861_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4848_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4848_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4864_ == 0)
{
v___x_4866_ = v___x_4863_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4812_);
lean_dec_ref(v_proof_4810_);
return v___x_4826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4869_, lean_object* v_generation_4870_, lean_object* v_p_4871_, lean_object* v_isNeg_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
uint8_t v_isNeg_boxed_4884_; lean_object* v_res_4885_; 
v_isNeg_boxed_4884_ = lean_unbox(v_isNeg_4872_);
v_res_4885_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4869_, v_generation_4870_, v_p_4871_, v_isNeg_boxed_4884_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_);
lean_dec(v_a_4882_);
lean_dec_ref(v_a_4881_);
lean_dec(v_a_4880_);
lean_dec_ref(v_a_4879_);
lean_dec(v_a_4878_);
lean_dec_ref(v_a_4877_);
lean_dec(v_a_4876_);
lean_dec_ref(v_a_4875_);
lean_dec(v_a_4874_);
lean_dec(v_a_4873_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4886_, lean_object* v_generation_4887_, lean_object* v_p_4888_, lean_object* v_lhs_4889_, lean_object* v_rhs_4890_, uint8_t v_isNeg_4891_, uint8_t v_isHEq_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_){
_start:
{
if (v_isNeg_4891_ == 0)
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
lean_inc_ref(v_p_4888_);
v___x_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4904_, 0, v_p_4888_);
lean_inc(v_a_4902_);
lean_inc_ref(v_a_4901_);
lean_inc(v_a_4900_);
lean_inc_ref(v_a_4899_);
lean_inc(v_a_4898_);
lean_inc_ref(v_a_4897_);
lean_inc(v_a_4896_);
lean_inc_ref(v_a_4895_);
lean_inc(v_a_4894_);
lean_inc(v_a_4893_);
lean_inc_ref(v___x_4904_);
lean_inc(v_generation_4887_);
lean_inc_ref(v_lhs_4889_);
v___x_4905_ = lean_grind_internalize(v_lhs_4889_, v_generation_4887_, v___x_4904_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
if (lean_obj_tag(v___x_4905_) == 0)
{
lean_object* v___x_4906_; 
lean_dec_ref_known(v___x_4905_, 1);
lean_inc(v_a_4902_);
lean_inc_ref(v_a_4901_);
lean_inc(v_a_4900_);
lean_inc_ref(v_a_4899_);
lean_inc(v_a_4898_);
lean_inc_ref(v_a_4897_);
lean_inc(v_a_4896_);
lean_inc_ref(v_a_4895_);
lean_inc(v_a_4894_);
lean_inc(v_a_4893_);
lean_inc_ref(v_rhs_4890_);
v___x_4906_ = lean_grind_internalize(v_rhs_4890_, v_generation_4887_, v___x_4904_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
lean_dec_ref_known(v___x_4906_, 1);
v___x_4907_ = lean_box(0);
v___x_4908_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4888_, v___x_4907_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v___x_4909_; 
lean_dec_ref_known(v___x_4908_, 1);
v___x_4909_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4889_, v_rhs_4890_, v_proof_4886_, v_isHEq_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
return v___x_4909_;
}
else
{
lean_dec_ref(v_rhs_4890_);
lean_dec_ref(v_lhs_4889_);
lean_dec_ref(v_proof_4886_);
return v___x_4908_;
}
}
else
{
lean_dec_ref(v_rhs_4890_);
lean_dec_ref(v_lhs_4889_);
lean_dec_ref(v_p_4888_);
lean_dec_ref(v_proof_4886_);
return v___x_4906_;
}
}
else
{
lean_dec_ref_known(v___x_4904_, 1);
lean_dec_ref(v_rhs_4890_);
lean_dec_ref(v_lhs_4889_);
lean_dec_ref(v_p_4888_);
lean_dec(v_generation_4887_);
lean_dec_ref(v_proof_4886_);
return v___x_4905_;
}
}
else
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
lean_dec_ref(v_rhs_4890_);
lean_dec_ref(v_lhs_4889_);
v___x_4910_ = lean_box(0);
lean_inc(v_a_4902_);
lean_inc_ref(v_a_4901_);
lean_inc(v_a_4900_);
lean_inc_ref(v_a_4899_);
lean_inc(v_a_4898_);
lean_inc_ref(v_a_4897_);
lean_inc(v_a_4896_);
lean_inc_ref(v_a_4895_);
lean_inc(v_a_4894_);
lean_inc(v_a_4893_);
lean_inc_ref(v_p_4888_);
v___x_4911_ = lean_grind_internalize(v_p_4888_, v_generation_4887_, v___x_4910_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v___x_4912_; 
lean_dec_ref_known(v___x_4911_, 1);
v___x_4912_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4897_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4914_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
v___x_4914_ = l_Lean_Meta_mkEqFalse(v_proof_4886_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4916_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc(v_a_4915_);
lean_dec_ref_known(v___x_4914_, 1);
v___x_4916_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4888_, v_a_4913_, v_a_4915_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
return v___x_4916_;
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
lean_dec(v_a_4913_);
lean_dec_ref(v_p_4888_);
v_a_4917_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4914_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4914_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4932_; 
lean_dec_ref(v_p_4888_);
lean_dec_ref(v_proof_4886_);
v_a_4925_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4927_ = v___x_4912_;
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4912_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
if (v_isShared_4928_ == 0)
{
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4925_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
}
else
{
lean_dec_ref(v_p_4888_);
lean_dec_ref(v_proof_4886_);
return v___x_4911_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4933_ = _args[0];
lean_object* v_generation_4934_ = _args[1];
lean_object* v_p_4935_ = _args[2];
lean_object* v_lhs_4936_ = _args[3];
lean_object* v_rhs_4937_ = _args[4];
lean_object* v_isNeg_4938_ = _args[5];
lean_object* v_isHEq_4939_ = _args[6];
lean_object* v_a_4940_ = _args[7];
lean_object* v_a_4941_ = _args[8];
lean_object* v_a_4942_ = _args[9];
lean_object* v_a_4943_ = _args[10];
lean_object* v_a_4944_ = _args[11];
lean_object* v_a_4945_ = _args[12];
lean_object* v_a_4946_ = _args[13];
lean_object* v_a_4947_ = _args[14];
lean_object* v_a_4948_ = _args[15];
lean_object* v_a_4949_ = _args[16];
lean_object* v_a_4950_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4951_; uint8_t v_isHEq_boxed_4952_; lean_object* v_res_4953_; 
v_isNeg_boxed_4951_ = lean_unbox(v_isNeg_4938_);
v_isHEq_boxed_4952_ = lean_unbox(v_isHEq_4939_);
v_res_4953_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4933_, v_generation_4934_, v_p_4935_, v_lhs_4936_, v_rhs_4937_, v_isNeg_boxed_4951_, v_isHEq_boxed_4952_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_);
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
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4957_, lean_object* v_generation_4958_, lean_object* v_p_4959_, uint8_t v_isNeg_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v___x_4972_; 
lean_inc_ref(v_p_4959_);
v___x_4972_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4959_, v_a_4968_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v_a_4973_; lean_object* v___x_4974_; uint8_t v___x_4975_; 
v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
lean_inc(v_a_4973_);
lean_dec_ref_known(v___x_4972_, 1);
v___x_4974_ = l_Lean_Expr_cleanupAnnotations(v_a_4973_);
v___x_4975_ = l_Lean_Expr_isApp(v___x_4974_);
if (v___x_4975_ == 0)
{
lean_object* v___x_4976_; 
lean_dec_ref(v___x_4974_);
v___x_4976_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4957_, v_generation_4958_, v_p_4959_, v_isNeg_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
return v___x_4976_;
}
else
{
lean_object* v_arg_4977_; lean_object* v___x_4978_; uint8_t v___x_4979_; 
v_arg_4977_ = lean_ctor_get(v___x_4974_, 1);
lean_inc_ref(v_arg_4977_);
v___x_4978_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4974_);
v___x_4979_ = l_Lean_Expr_isApp(v___x_4978_);
if (v___x_4979_ == 0)
{
lean_object* v___x_4980_; 
lean_dec_ref(v___x_4978_);
lean_dec_ref(v_arg_4977_);
v___x_4980_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4957_, v_generation_4958_, v_p_4959_, v_isNeg_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
return v___x_4980_;
}
else
{
lean_object* v_arg_4981_; lean_object* v___x_4982_; uint8_t v___x_4983_; 
v_arg_4981_ = lean_ctor_get(v___x_4978_, 1);
lean_inc_ref(v_arg_4981_);
v___x_4982_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4978_);
v___x_4983_ = l_Lean_Expr_isApp(v___x_4982_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4984_; 
lean_dec_ref(v___x_4982_);
lean_dec_ref(v_arg_4981_);
lean_dec_ref(v_arg_4977_);
v___x_4984_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4957_, v_generation_4958_, v_p_4959_, v_isNeg_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
return v___x_4984_;
}
else
{
lean_object* v_arg_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; uint8_t v___x_4988_; 
v_arg_4985_ = lean_ctor_get(v___x_4982_, 1);
lean_inc_ref(v_arg_4985_);
v___x_4986_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4982_);
v___x_4987_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_4988_ = l_Lean_Expr_isConstOf(v___x_4986_, v___x_4987_);
if (v___x_4988_ == 0)
{
uint8_t v___x_4989_; 
lean_dec_ref(v_arg_4981_);
v___x_4989_ = l_Lean_Expr_isApp(v___x_4986_);
if (v___x_4989_ == 0)
{
lean_object* v___x_4990_; 
lean_dec_ref(v___x_4986_);
lean_dec_ref(v_arg_4985_);
lean_dec_ref(v_arg_4977_);
v___x_4990_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4957_, v_generation_4958_, v_p_4959_, v_isNeg_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
return v___x_4990_;
}
else
{
lean_object* v___x_4991_; lean_object* v___x_4992_; uint8_t v___x_4993_; 
v___x_4991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4986_);
v___x_4992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_4993_ = l_Lean_Expr_isConstOf(v___x_4991_, v___x_4992_);
lean_dec_ref(v___x_4991_);
if (v___x_4993_ == 0)
{
lean_object* v___x_4994_; 
lean_dec_ref(v_arg_4985_);
lean_dec_ref(v_arg_4977_);
v___x_4994_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4957_, v_generation_4958_, v_p_4959_, v_isNeg_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
return v___x_4994_;
}
else
{
lean_object* v___x_4995_; 
v___x_4995_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4957_, v_generation_4958_, v_p_4959_, v_arg_4985_, v_arg_4977_, v_isNeg_4960_, v___x_4993_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
return v___x_4995_;
}
}
}
else
{
uint8_t v___x_4996_; 
lean_dec_ref(v___x_4986_);
v___x_4996_ = l_Lean_Expr_isProp(v_arg_4985_);
lean_dec_ref(v_arg_4985_);
if (v___x_4996_ == 0)
{
lean_object* v___x_4997_; 
v___x_4997_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4957_, v_generation_4958_, v_p_4959_, v_arg_4981_, v_arg_4977_, v_isNeg_4960_, v___x_4996_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
return v___x_4997_;
}
else
{
lean_object* v___x_4998_; 
lean_dec_ref(v_arg_4981_);
lean_dec_ref(v_arg_4977_);
v___x_4998_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4957_, v_generation_4958_, v_p_4959_, v_isNeg_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
return v___x_4998_;
}
}
}
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec_ref(v_p_4959_);
lean_dec(v_generation_4958_);
lean_dec_ref(v_proof_4957_);
v_a_4999_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4972_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4972_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5007_, lean_object* v_generation_5008_, lean_object* v_p_5009_, lean_object* v_isNeg_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_){
_start:
{
uint8_t v_isNeg_boxed_5022_; lean_object* v_res_5023_; 
v_isNeg_boxed_5022_ = lean_unbox(v_isNeg_5010_);
v_res_5023_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5007_, v_generation_5008_, v_p_5009_, v_isNeg_boxed_5022_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
lean_dec(v_a_5020_);
lean_dec_ref(v_a_5019_);
lean_dec(v_a_5018_);
lean_dec_ref(v_a_5017_);
lean_dec(v_a_5016_);
lean_dec_ref(v_a_5015_);
lean_dec(v_a_5014_);
lean_dec_ref(v_a_5013_);
lean_dec(v_a_5012_);
lean_dec(v_a_5011_);
return v_res_5023_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5032_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5033_ = l_Lean_Name_append(v___x_5032_, v___x_5031_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5034_, lean_object* v_proof_5035_, lean_object* v_generation_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_){
_start:
{
lean_object* v___y_5049_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v___y_5052_; lean_object* v___y_5053_; lean_object* v___y_5054_; lean_object* v___y_5055_; lean_object* v___y_5056_; lean_object* v___y_5057_; lean_object* v___y_5058_; lean_object* v___y_5062_; lean_object* v___y_5063_; lean_object* v___y_5064_; lean_object* v___y_5065_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___x_5079_; lean_object* v_toCold_5080_; lean_object* v_options_5081_; uint8_t v_hasTrace_5082_; 
lean_inc_ref(v_fact_5034_);
v___x_5079_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5034_, v_a_5037_);
lean_dec_ref(v___x_5079_);
v_toCold_5080_ = lean_ctor_get(v_a_5045_, 0);
v_options_5081_ = lean_ctor_get(v_toCold_5080_, 2);
v_hasTrace_5082_ = lean_ctor_get_uint8(v_options_5081_, sizeof(void*)*1);
if (v_hasTrace_5082_ == 0)
{
v___y_5062_ = v_a_5037_;
v___y_5063_ = v_a_5038_;
v___y_5064_ = v_a_5039_;
v___y_5065_ = v_a_5040_;
v___y_5066_ = v_a_5041_;
v___y_5067_ = v_a_5042_;
v___y_5068_ = v_a_5043_;
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
goto v___jp_5061_;
}
else
{
lean_object* v_inheritedTraceOptions_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; uint8_t v___x_5086_; 
v_inheritedTraceOptions_5083_ = lean_ctor_get(v_toCold_5080_, 11);
v___x_5084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5085_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5086_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5083_, v_options_5081_, v___x_5085_);
if (v___x_5086_ == 0)
{
v___y_5062_ = v_a_5037_;
v___y_5063_ = v_a_5038_;
v___y_5064_ = v_a_5039_;
v___y_5065_ = v_a_5040_;
v___y_5066_ = v_a_5041_;
v___y_5067_ = v_a_5042_;
v___y_5068_ = v_a_5043_;
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
goto v___jp_5061_;
}
else
{
lean_object* v___x_5087_; 
v___x_5087_ = l_Lean_Meta_Grind_updateLastTag(v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v___x_5088_; lean_object* v___x_5089_; 
lean_dec_ref_known(v___x_5087_, 1);
lean_inc_ref(v_fact_5034_);
v___x_5088_ = l_Lean_MessageData_ofExpr(v_fact_5034_);
v___x_5089_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5084_, v___x_5088_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_);
if (lean_obj_tag(v___x_5089_) == 0)
{
lean_dec_ref_known(v___x_5089_, 1);
v___y_5062_ = v_a_5037_;
v___y_5063_ = v_a_5038_;
v___y_5064_ = v_a_5039_;
v___y_5065_ = v_a_5040_;
v___y_5066_ = v_a_5041_;
v___y_5067_ = v_a_5042_;
v___y_5068_ = v_a_5043_;
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
goto v___jp_5061_;
}
else
{
lean_dec(v_generation_5036_);
lean_dec_ref(v_proof_5035_);
lean_dec_ref(v_fact_5034_);
return v___x_5089_;
}
}
else
{
lean_dec(v_generation_5036_);
lean_dec_ref(v_proof_5035_);
lean_dec_ref(v_fact_5034_);
return v___x_5087_;
}
}
}
v___jp_5048_:
{
uint8_t v___x_5059_; lean_object* v___x_5060_; 
v___x_5059_ = 0;
v___x_5060_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5035_, v_generation_5036_, v_fact_5034_, v___x_5059_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
return v___x_5060_;
}
v___jp_5061_:
{
lean_object* v___x_5072_; uint8_t v___x_5073_; 
lean_inc_ref(v_fact_5034_);
v___x_5072_ = l_Lean_Expr_cleanupAnnotations(v_fact_5034_);
v___x_5073_ = l_Lean_Expr_isApp(v___x_5072_);
if (v___x_5073_ == 0)
{
lean_dec_ref(v___x_5072_);
v___y_5049_ = v___y_5062_;
v___y_5050_ = v___y_5063_;
v___y_5051_ = v___y_5064_;
v___y_5052_ = v___y_5065_;
v___y_5053_ = v___y_5066_;
v___y_5054_ = v___y_5067_;
v___y_5055_ = v___y_5068_;
v___y_5056_ = v___y_5069_;
v___y_5057_ = v___y_5070_;
v___y_5058_ = v___y_5071_;
goto v___jp_5048_;
}
else
{
lean_object* v_arg_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; uint8_t v___x_5077_; 
v_arg_5074_ = lean_ctor_get(v___x_5072_, 1);
lean_inc_ref(v_arg_5074_);
v___x_5075_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5072_);
v___x_5076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5077_ = l_Lean_Expr_isConstOf(v___x_5075_, v___x_5076_);
lean_dec_ref(v___x_5075_);
if (v___x_5077_ == 0)
{
lean_dec_ref(v_arg_5074_);
v___y_5049_ = v___y_5062_;
v___y_5050_ = v___y_5063_;
v___y_5051_ = v___y_5064_;
v___y_5052_ = v___y_5065_;
v___y_5053_ = v___y_5066_;
v___y_5054_ = v___y_5067_;
v___y_5055_ = v___y_5068_;
v___y_5056_ = v___y_5069_;
v___y_5057_ = v___y_5070_;
v___y_5058_ = v___y_5071_;
goto v___jp_5048_;
}
else
{
lean_object* v___x_5078_; 
lean_dec_ref(v_fact_5034_);
v___x_5078_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5035_, v_generation_5036_, v_arg_5074_, v___x_5077_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_);
return v___x_5078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5090_, lean_object* v_proof_5091_, lean_object* v_generation_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_){
_start:
{
lean_object* v_res_5104_; 
v_res_5104_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5090_, v_proof_5091_, v_generation_5092_, v_a_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
lean_dec(v_a_5102_);
lean_dec_ref(v_a_5101_);
lean_dec(v_a_5100_);
lean_dec_ref(v_a_5099_);
lean_dec(v_a_5098_);
lean_dec_ref(v_a_5097_);
lean_dec(v_a_5096_);
lean_dec_ref(v_a_5095_);
lean_dec(v_a_5094_);
lean_dec(v_a_5093_);
return v_res_5104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_){
_start:
{
lean_object* v___x_5119_; 
v___x_5119_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5108_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v_a_5120_; uint8_t v___x_5121_; 
v_a_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_a_5120_);
lean_dec_ref_known(v___x_5119_, 1);
v___x_5121_ = lean_unbox(v_a_5120_);
lean_dec(v_a_5120_);
if (v___x_5121_ == 0)
{
lean_object* v___x_5122_; lean_object* v___x_5123_; 
v___x_5122_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5123_ = l_Lean_Core_checkSystem(v___x_5122_, v___y_5116_, v___y_5117_);
if (lean_obj_tag(v___x_5123_) == 0)
{
lean_object* v___x_5124_; 
lean_dec_ref_known(v___x_5123_, 1);
v___x_5124_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5108_);
if (lean_obj_tag(v___x_5124_) == 0)
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5161_; 
v_a_5125_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5127_ = v___x_5124_;
v_isShared_5128_ = v_isSharedCheck_5161_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5124_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5161_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
if (lean_obj_tag(v_a_5125_) == 1)
{
lean_object* v_val_5129_; 
lean_del_object(v___x_5127_);
v_val_5129_ = lean_ctor_get(v_a_5125_, 0);
lean_inc(v_val_5129_);
lean_dec_ref_known(v_a_5125_, 1);
if (lean_obj_tag(v_val_5129_) == 0)
{
lean_object* v_lhs_5130_; lean_object* v_rhs_5131_; lean_object* v_proof_5132_; uint8_t v_isHEq_5133_; lean_object* v___x_5134_; 
v_lhs_5130_ = lean_ctor_get(v_val_5129_, 0);
lean_inc_ref(v_lhs_5130_);
v_rhs_5131_ = lean_ctor_get(v_val_5129_, 1);
lean_inc_ref(v_rhs_5131_);
v_proof_5132_ = lean_ctor_get(v_val_5129_, 2);
lean_inc_ref(v_proof_5132_);
v_isHEq_5133_ = lean_ctor_get_uint8(v_val_5129_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5129_, 3);
v___x_5134_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5130_, v_rhs_5131_, v_proof_5132_, v_isHEq_5133_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_dec_ref_known(v___x_5134_, 1);
goto _start;
}
else
{
lean_object* v_a_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
v_a_5136_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5138_ = v___x_5134_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_a_5136_);
lean_dec(v___x_5134_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5136_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
}
else
{
lean_object* v_prop_5144_; lean_object* v_proof_5145_; lean_object* v_generation_5146_; lean_object* v___x_5147_; 
v_prop_5144_ = lean_ctor_get(v_val_5129_, 0);
lean_inc_ref(v_prop_5144_);
v_proof_5145_ = lean_ctor_get(v_val_5129_, 1);
lean_inc_ref(v_proof_5145_);
v_generation_5146_ = lean_ctor_get(v_val_5129_, 2);
lean_inc(v_generation_5146_);
lean_dec_ref_known(v_val_5129_, 3);
v___x_5147_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5144_, v_proof_5145_, v_generation_5146_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_dec_ref_known(v___x_5147_, 1);
goto _start;
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
v_a_5149_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5147_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5147_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
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
}
else
{
lean_object* v___x_5157_; lean_object* v___x_5159_; 
lean_dec(v_a_5125_);
v___x_5157_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5128_ == 0)
{
lean_ctor_set(v___x_5127_, 0, v___x_5157_);
v___x_5159_ = v___x_5127_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v___x_5157_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
}
}
else
{
lean_object* v_a_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5169_; 
v_a_5162_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5164_ = v___x_5124_;
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_a_5162_);
lean_dec(v___x_5124_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5167_; 
if (v_isShared_5165_ == 0)
{
v___x_5167_ = v___x_5164_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5162_);
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
v_a_5170_ = lean_ctor_get(v___x_5123_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_5123_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5172_ = v___x_5123_;
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_a_5170_);
lean_dec(v___x_5123_);
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
else
{
lean_object* v___x_5178_; 
v___x_5178_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5108_);
if (lean_obj_tag(v___x_5178_) == 0)
{
lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5186_; 
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5186_ == 0)
{
lean_object* v_unused_5187_; 
v_unused_5187_ = lean_ctor_get(v___x_5178_, 0);
lean_dec(v_unused_5187_);
v___x_5180_ = v___x_5178_;
v_isShared_5181_ = v_isSharedCheck_5186_;
goto v_resetjp_5179_;
}
else
{
lean_dec(v___x_5178_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5186_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5182_; lean_object* v___x_5184_; 
v___x_5182_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5181_ == 0)
{
lean_ctor_set(v___x_5180_, 0, v___x_5182_);
v___x_5184_ = v___x_5180_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v___x_5182_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
else
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5195_; 
v_a_5188_ = lean_ctor_get(v___x_5178_, 0);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5190_ = v___x_5178_;
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_dec(v___x_5178_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5191_ == 0)
{
v___x_5193_ = v___x_5190_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5188_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
}
}
else
{
lean_object* v_a_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5203_; 
v_a_5196_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5198_ = v___x_5119_;
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_a_5196_);
lean_dec(v___x_5119_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5201_; 
if (v_isShared_5199_ == 0)
{
v___x_5201_ = v___x_5198_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_a_5196_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
lean_object* v_res_5215_; 
v_res_5215_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
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
return v_res_5215_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_){
_start:
{
lean_object* v___x_5227_; lean_object* v___x_5228_; 
v___x_5227_ = lean_box(0);
v___x_5228_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_);
lean_dec(v_a_5225_);
lean_dec_ref(v_a_5224_);
lean_dec(v_a_5223_);
lean_dec_ref(v_a_5222_);
lean_dec(v_a_5221_);
lean_dec_ref(v_a_5220_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_a_5217_);
lean_dec(v_a_5216_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v_a_5229_; lean_object* v___x_5231_; uint8_t v_isShared_5232_; uint8_t v_isSharedCheck_5241_; 
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5231_ = v___x_5228_;
v_isShared_5232_ = v_isSharedCheck_5241_;
goto v_resetjp_5230_;
}
else
{
lean_inc(v_a_5229_);
lean_dec(v___x_5228_);
v___x_5231_ = lean_box(0);
v_isShared_5232_ = v_isSharedCheck_5241_;
goto v_resetjp_5230_;
}
v_resetjp_5230_:
{
lean_object* v_fst_5233_; 
v_fst_5233_ = lean_ctor_get(v_a_5229_, 0);
lean_inc(v_fst_5233_);
lean_dec(v_a_5229_);
if (lean_obj_tag(v_fst_5233_) == 0)
{
lean_object* v___x_5235_; 
if (v_isShared_5232_ == 0)
{
lean_ctor_set(v___x_5231_, 0, v___x_5227_);
v___x_5235_ = v___x_5231_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v___x_5227_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
else
{
lean_object* v_val_5237_; lean_object* v___x_5239_; 
v_val_5237_ = lean_ctor_get(v_fst_5233_, 0);
lean_inc(v_val_5237_);
lean_dec_ref_known(v_fst_5233_, 1);
if (v_isShared_5232_ == 0)
{
lean_ctor_set(v___x_5231_, 0, v_val_5237_);
v___x_5239_ = v___x_5231_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v_val_5237_);
v___x_5239_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
return v___x_5239_;
}
}
}
}
else
{
lean_object* v_a_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5249_; 
v_a_5242_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5244_ = v___x_5228_;
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_a_5242_);
lean_dec(v___x_5228_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5247_; 
if (v_isShared_5245_ == 0)
{
v___x_5247_ = v___x_5244_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = lean_grind_process_new_facts(v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_inst_5262_, lean_object* v_a_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
lean_object* v___x_5275_; 
v___x_5275_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_);
return v___x_5275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_inst_5276_, lean_object* v_a_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_inst_5276_, v_a_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
lean_dec(v___y_5285_);
lean_dec_ref(v___y_5284_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v___y_5279_);
lean_dec(v___y_5278_);
lean_dec_ref(v_a_5277_);
return v_res_5289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5290_, lean_object* v_proof_5291_, lean_object* v_generation_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_){
_start:
{
uint8_t v___x_5304_; 
lean_inc_ref(v_fact_5290_);
v___x_5304_ = l_Lean_Expr_isTrue(v_fact_5290_);
if (v___x_5304_ == 0)
{
lean_object* v___x_5305_; 
v___x_5305_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5293_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5317_; 
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5308_ = v___x_5305_;
v_isShared_5309_ = v_isSharedCheck_5317_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5305_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5317_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
uint8_t v___x_5310_; 
v___x_5310_ = lean_unbox(v_a_5306_);
lean_dec(v_a_5306_);
if (v___x_5310_ == 0)
{
lean_object* v___x_5311_; lean_object* v___x_5312_; 
lean_del_object(v___x_5308_);
v___x_5311_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5293_);
lean_dec_ref(v___x_5311_);
v___x_5312_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5290_, v_proof_5291_, v_generation_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_);
return v___x_5312_;
}
else
{
lean_object* v___x_5313_; lean_object* v___x_5315_; 
lean_dec(v_generation_5292_);
lean_dec_ref(v_proof_5291_);
lean_dec_ref(v_fact_5290_);
v___x_5313_ = lean_box(0);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 0, v___x_5313_);
v___x_5315_ = v___x_5308_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5313_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
}
}
else
{
lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5325_; 
lean_dec(v_generation_5292_);
lean_dec_ref(v_proof_5291_);
lean_dec_ref(v_fact_5290_);
v_a_5318_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5320_ = v___x_5305_;
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v___x_5305_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5318_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
}
else
{
lean_object* v___x_5326_; lean_object* v___x_5327_; 
lean_dec(v_generation_5292_);
lean_dec_ref(v_proof_5291_);
lean_dec_ref(v_fact_5290_);
v___x_5326_ = lean_box(0);
v___x_5327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5326_);
return v___x_5327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5328_, lean_object* v_proof_5329_, lean_object* v_generation_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_){
_start:
{
lean_object* v_res_5342_; 
v_res_5342_ = l_Lean_Meta_Grind_add(v_fact_5328_, v_proof_5329_, v_generation_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_);
lean_dec(v_a_5340_);
lean_dec_ref(v_a_5339_);
lean_dec(v_a_5338_);
lean_dec_ref(v_a_5337_);
lean_dec(v_a_5336_);
lean_dec_ref(v_a_5335_);
lean_dec(v_a_5334_);
lean_dec_ref(v_a_5333_);
lean_dec(v_a_5332_);
lean_dec(v_a_5331_);
return v_res_5342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5343_, lean_object* v_generation_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_){
_start:
{
lean_object* v___x_5356_; 
lean_inc(v_fvarId_5343_);
v___x_5356_ = l_Lean_FVarId_getType___redArg(v_fvarId_5343_, v_a_5351_, v_a_5353_, v_a_5354_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_a_5357_);
lean_dec_ref_known(v___x_5356_, 1);
v___x_5358_ = l_Lean_mkFVar(v_fvarId_5343_);
v___x_5359_ = l_Lean_Meta_Grind_add(v_a_5357_, v___x_5358_, v_generation_5344_, v_a_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_);
return v___x_5359_;
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec(v_generation_5344_);
lean_dec(v_fvarId_5343_);
v_a_5360_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5356_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5356_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5368_, lean_object* v_generation_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_){
_start:
{
lean_object* v_res_5381_; 
v_res_5381_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5368_, v_generation_5369_, v_a_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_);
lean_dec(v_a_5379_);
lean_dec_ref(v_a_5378_);
lean_dec(v_a_5377_);
lean_dec_ref(v_a_5376_);
lean_dec(v_a_5375_);
lean_dec_ref(v_a_5374_);
lean_dec(v_a_5373_);
lean_dec_ref(v_a_5372_);
lean_dec(v_a_5371_);
lean_dec(v_a_5370_);
return v_res_5381_;
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
