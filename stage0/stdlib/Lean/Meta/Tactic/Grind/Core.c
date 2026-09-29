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
lean_object* v_ref_193_; lean_object* v___x_194_; lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_240_; 
v_ref_193_ = lean_ctor_get(v___y_190_, 2);
v___x_194_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1_spec__2(v_msg_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_240_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_240_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_240_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v_traceState_200_; lean_object* v_env_201_; lean_object* v_nextMacroScope_202_; lean_object* v_ngen_203_; lean_object* v_auxDeclNGen_204_; lean_object* v_cache_205_; lean_object* v_recordedDeps_206_; lean_object* v_messages_207_; lean_object* v_infoState_208_; lean_object* v_snapshotTasks_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_239_; 
v___x_199_ = lean_st_ref_take(v___y_191_);
v_traceState_200_ = lean_ctor_get(v___x_199_, 4);
v_env_201_ = lean_ctor_get(v___x_199_, 0);
v_nextMacroScope_202_ = lean_ctor_get(v___x_199_, 1);
v_ngen_203_ = lean_ctor_get(v___x_199_, 2);
v_auxDeclNGen_204_ = lean_ctor_get(v___x_199_, 3);
v_cache_205_ = lean_ctor_get(v___x_199_, 5);
v_recordedDeps_206_ = lean_ctor_get(v___x_199_, 6);
v_messages_207_ = lean_ctor_get(v___x_199_, 7);
v_infoState_208_ = lean_ctor_get(v___x_199_, 8);
v_snapshotTasks_209_ = lean_ctor_get(v___x_199_, 9);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_239_ == 0)
{
v___x_211_ = v___x_199_;
v_isShared_212_ = v_isSharedCheck_239_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_snapshotTasks_209_);
lean_inc(v_infoState_208_);
lean_inc(v_messages_207_);
lean_inc(v_recordedDeps_206_);
lean_inc(v_cache_205_);
lean_inc(v_traceState_200_);
lean_inc(v_auxDeclNGen_204_);
lean_inc(v_ngen_203_);
lean_inc(v_nextMacroScope_202_);
lean_inc(v_env_201_);
lean_dec(v___x_199_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_239_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
uint64_t v_tid_213_; lean_object* v_traces_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_238_; 
v_tid_213_ = lean_ctor_get_uint64(v_traceState_200_, sizeof(void*)*1);
v_traces_214_ = lean_ctor_get(v_traceState_200_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v_traceState_200_);
if (v_isSharedCheck_238_ == 0)
{
v___x_216_ = v_traceState_200_;
v_isShared_217_ = v_isSharedCheck_238_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_traces_214_);
lean_dec(v_traceState_200_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_238_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_219_; double v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_218_ = lean_box(0);
v___x_219_ = lean_box(0);
v___x_220_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__0);
v___x_221_ = 0;
v___x_222_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__1));
v___x_223_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_223_, 0, v_cls_186_);
lean_ctor_set(v___x_223_, 1, v___x_219_);
lean_ctor_set(v___x_223_, 2, v___x_222_);
lean_ctor_set_float(v___x_223_, sizeof(void*)*3, v___x_220_);
lean_ctor_set_float(v___x_223_, sizeof(void*)*3 + 8, v___x_220_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*3 + 16, v___x_221_);
v___x_224_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___closed__2));
v___x_225_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v_a_195_);
lean_ctor_set(v___x_225_, 2, v___x_224_);
lean_inc(v_ref_193_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_ref_193_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = l_Lean_PersistentArray_push___redArg(v_traces_214_, v___x_226_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_227_);
v___x_229_ = v___x_216_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_227_);
lean_ctor_set_uint64(v_reuseFailAlloc_237_, sizeof(void*)*1, v_tid_213_);
v___x_229_ = v_reuseFailAlloc_237_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_231_; 
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 4, v___x_229_);
v___x_231_ = v___x_211_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_env_201_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_nextMacroScope_202_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_ngen_203_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_auxDeclNGen_204_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_236_, 5, v_cache_205_);
lean_ctor_set(v_reuseFailAlloc_236_, 6, v_recordedDeps_206_);
lean_ctor_set(v_reuseFailAlloc_236_, 7, v_messages_207_);
lean_ctor_set(v_reuseFailAlloc_236_, 8, v_infoState_208_);
lean_ctor_set(v_reuseFailAlloc_236_, 9, v_snapshotTasks_209_);
v___x_231_ = v_reuseFailAlloc_236_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_st_ref_put(v___y_191_, v___x_231_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_218_);
v___x_234_ = v___x_197_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_218_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg___boxed(lean_object* v_cls_241_, lean_object* v_msg_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_241_, v_msg_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(lean_object* v___x_249_, lean_object* v_xs_250_, lean_object* v_v_251_, lean_object* v_i_252_){
_start:
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_array_get_size(v_xs_250_);
v___x_254_ = lean_nat_dec_lt(v_i_252_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v_i_252_);
lean_dec_ref(v_v_251_);
v___x_255_ = lean_box(0);
return v___x_255_;
}
else
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_array_fget_borrowed(v_xs_250_, v_i_252_);
lean_inc_ref(v_v_251_);
lean_inc(v___x_256_);
v___x_257_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_249_, v___x_256_, v_v_251_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_add(v_i_252_, v___x_258_);
lean_dec(v_i_252_);
v_i_252_ = v___x_259_;
goto _start;
}
else
{
lean_object* v___x_261_; 
lean_dec_ref(v_v_251_);
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v_i_252_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v___x_262_, lean_object* v_xs_263_, lean_object* v_v_264_, lean_object* v_i_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_262_, v_xs_263_, v_v_264_, v_i_265_);
lean_dec_ref(v_xs_263_);
lean_dec_ref(v___x_262_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(lean_object* v___x_267_, lean_object* v_xs_268_, lean_object* v_v_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1_spec__5(v___x_267_, v_xs_268_, v_v_269_, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1___boxed(lean_object* v___x_272_, lean_object* v_xs_273_, lean_object* v_v_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_272_, v_xs_273_, v_v_274_);
lean_dec_ref(v_xs_273_);
lean_dec_ref(v___x_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(lean_object* v___x_276_, lean_object* v_x_277_, size_t v_x_278_, lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v_es_280_; lean_object* v___x_281_; size_t v___x_282_; size_t v___x_283_; lean_object* v_j_284_; lean_object* v_entry_285_; 
v_es_280_ = lean_ctor_get(v_x_277_, 0);
v___x_281_ = lean_box(2);
v___x_282_ = ((size_t)31ULL);
v___x_283_ = lean_usize_land(v_x_278_, v___x_282_);
v_j_284_ = lean_usize_to_nat(v___x_283_);
v_entry_285_ = lean_array_get(v___x_281_, v_es_280_, v_j_284_);
switch(lean_obj_tag(v_entry_285_))
{
case 0:
{
lean_object* v_key_286_; uint8_t v___x_287_; 
v_key_286_ = lean_ctor_get(v_entry_285_, 0);
lean_inc(v_key_286_);
lean_dec_ref_known(v_entry_285_, 2);
v___x_287_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_276_, v_x_279_, v_key_286_);
if (v___x_287_ == 0)
{
lean_dec(v_j_284_);
return v_x_277_;
}
else
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_295_; 
lean_inc_ref(v_es_280_);
v_isSharedCheck_295_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; 
v_unused_296_ = lean_ctor_get(v_x_277_, 0);
lean_dec(v_unused_296_);
v___x_289_ = v_x_277_;
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
else
{
lean_dec(v_x_277_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = lean_array_set(v_es_280_, v_j_284_, v___x_281_);
lean_dec(v_j_284_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
case 1:
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_331_; 
lean_inc_ref(v_es_280_);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v_x_277_, 0);
lean_dec(v_unused_332_);
v___x_298_ = v_x_277_;
v_isShared_299_ = v_isSharedCheck_331_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_x_277_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_331_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v_node_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_330_; 
v_node_300_ = lean_ctor_get(v_entry_285_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_entry_285_);
if (v_isSharedCheck_330_ == 0)
{
v___x_302_ = v_entry_285_;
v_isShared_303_ = v_isSharedCheck_330_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_node_300_);
lean_dec(v_entry_285_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_330_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
size_t v___x_304_; lean_object* v_entries_305_; size_t v___x_306_; lean_object* v_newNode_307_; lean_object* v___x_308_; 
v___x_304_ = ((size_t)5ULL);
v_entries_305_ = lean_array_set(v_es_280_, v_j_284_, v___x_281_);
v___x_306_ = lean_usize_shift_right(v_x_278_, v___x_304_);
v_newNode_307_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_276_, v_node_300_, v___x_306_, v_x_279_);
lean_inc_ref(v_newNode_307_);
v___x_308_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_307_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_310_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v_newNode_307_);
v___x_310_ = v___x_302_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_newNode_307_);
v___x_310_ = v_reuseFailAlloc_315_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_array_set(v_entries_305_, v_j_284_, v___x_310_);
lean_dec(v_j_284_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_311_);
v___x_313_ = v___x_298_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v_val_316_; lean_object* v_fst_317_; lean_object* v_snd_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_329_; 
lean_dec_ref(v_newNode_307_);
lean_del_object(v___x_302_);
v_val_316_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_val_316_);
lean_dec_ref_known(v___x_308_, 1);
v_fst_317_ = lean_ctor_get(v_val_316_, 0);
v_snd_318_ = lean_ctor_get(v_val_316_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_val_316_);
if (v_isSharedCheck_329_ == 0)
{
v___x_320_ = v_val_316_;
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_snd_318_);
lean_inc(v_fst_317_);
lean_dec(v_val_316_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_329_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_fst_317_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_snd_318_);
v___x_323_ = v_reuseFailAlloc_328_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_324_ = lean_array_set(v_entries_305_, v_j_284_, v___x_323_);
lean_dec(v_j_284_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_324_);
v___x_326_ = v___x_298_;
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
}
}
}
}
default: 
{
lean_dec(v_j_284_);
lean_dec_ref(v_x_279_);
return v_x_277_;
}
}
}
else
{
lean_object* v_ks_333_; lean_object* v_vs_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_348_; 
v_ks_333_ = lean_ctor_get(v_x_277_, 0);
v_vs_334_ = lean_ctor_get(v_x_277_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_348_ == 0)
{
v___x_336_ = v_x_277_;
v_isShared_337_ = v_isSharedCheck_348_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_vs_334_);
lean_inc(v_ks_333_);
lean_dec(v_x_277_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_348_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_338_; 
v___x_338_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0_spec__1(v___x_276_, v_ks_333_, v_x_279_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_340_; 
if (v_isShared_337_ == 0)
{
v___x_340_ = v___x_336_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_ks_333_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_vs_334_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
else
{
lean_object* v_val_342_; lean_object* v_keys_x27_343_; lean_object* v_vals_x27_344_; lean_object* v___x_346_; 
v_val_342_ = lean_ctor_get(v___x_338_, 0);
lean_inc_n(v_val_342_, 2);
lean_dec_ref_known(v___x_338_, 1);
v_keys_x27_343_ = l_Array_eraseIdx___redArg(v_ks_333_, v_val_342_);
v_vals_x27_344_ = l_Array_eraseIdx___redArg(v_vs_334_, v_val_342_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_vals_x27_344_);
lean_ctor_set(v___x_336_, 0, v_keys_x27_343_);
v___x_346_ = v___x_336_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_keys_x27_343_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_vals_x27_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg___boxed(lean_object* v___x_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
size_t v_x_22633__boxed_353_; lean_object* v_res_354_; 
v_x_22633__boxed_353_ = lean_unbox_usize(v_x_351_);
lean_dec(v_x_351_);
v_res_354_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_349_, v_x_350_, v_x_22633__boxed_353_, v_x_352_);
lean_dec_ref(v___x_349_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(lean_object* v___x_355_, lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
uint64_t v___x_358_; size_t v_h_359_; lean_object* v___x_360_; 
lean_inc_ref(v_x_357_);
v___x_358_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_355_, v_x_357_);
v_h_359_ = lean_uint64_to_usize(v___x_358_);
v___x_360_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_355_, v_x_356_, v_h_359_, v_x_357_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg___boxed(lean_object* v___x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_361_, v_x_362_, v_x_363_);
lean_dec_ref(v___x_361_);
return v_res_364_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_376_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_377_ = l_Lean_Name_append(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__7));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(lean_object* v_as_x27_381_, lean_object* v_b_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
if (lean_obj_tag(v_as_x27_381_) == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v_b_382_);
return v___x_394_;
}
else
{
lean_object* v_head_395_; lean_object* v_tail_396_; lean_object* v___x_397_; lean_object* v___y_399_; uint8_t v_a_439_; uint8_t v___x_453_; 
v_head_395_ = lean_ctor_get(v_as_x27_381_, 0);
v_tail_396_ = lean_ctor_get(v_as_x27_381_, 1);
v___x_397_ = lean_box(0);
v___x_453_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_395_);
if (v___x_453_ == 0)
{
v_a_439_ = v___x_453_;
goto v___jp_438_;
}
else
{
lean_object* v___x_454_; 
lean_inc(v_head_395_);
v___x_454_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_395_, v___y_383_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; uint8_t v___x_456_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v___x_456_ = lean_unbox(v_a_455_);
lean_dec(v_a_455_);
v_a_439_ = v___x_456_;
goto v___jp_438_;
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_a_457_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_454_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_454_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
v___jp_398_:
{
lean_object* v___x_400_; lean_object* v_toGoalState_401_; lean_object* v_mvarId_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_437_; 
v___x_400_ = lean_st_ref_take(v___y_399_);
v_toGoalState_401_ = lean_ctor_get(v___x_400_, 0);
v_mvarId_402_ = lean_ctor_get(v___x_400_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_437_ == 0)
{
v___x_404_ = v___x_400_;
v_isShared_405_ = v_isSharedCheck_437_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_mvarId_402_);
lean_inc(v_toGoalState_401_);
lean_dec(v___x_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_437_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_nextDeclIdx_406_; lean_object* v_enodeMap_407_; lean_object* v_exprs_408_; lean_object* v_parents_409_; lean_object* v_congrTable_410_; lean_object* v_appMap_411_; lean_object* v_indicesFound_412_; lean_object* v_newFacts_413_; uint8_t v_inconsistent_414_; lean_object* v_nextIdx_415_; lean_object* v_newRawFacts_416_; lean_object* v_facts_417_; lean_object* v_extThms_418_; lean_object* v_ematch_419_; lean_object* v_inj_420_; lean_object* v_split_421_; lean_object* v_clean_422_; lean_object* v_sstates_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_436_; 
v_nextDeclIdx_406_ = lean_ctor_get(v_toGoalState_401_, 0);
v_enodeMap_407_ = lean_ctor_get(v_toGoalState_401_, 1);
v_exprs_408_ = lean_ctor_get(v_toGoalState_401_, 2);
v_parents_409_ = lean_ctor_get(v_toGoalState_401_, 3);
v_congrTable_410_ = lean_ctor_get(v_toGoalState_401_, 4);
v_appMap_411_ = lean_ctor_get(v_toGoalState_401_, 5);
v_indicesFound_412_ = lean_ctor_get(v_toGoalState_401_, 6);
v_newFacts_413_ = lean_ctor_get(v_toGoalState_401_, 7);
v_inconsistent_414_ = lean_ctor_get_uint8(v_toGoalState_401_, sizeof(void*)*17);
v_nextIdx_415_ = lean_ctor_get(v_toGoalState_401_, 8);
v_newRawFacts_416_ = lean_ctor_get(v_toGoalState_401_, 9);
v_facts_417_ = lean_ctor_get(v_toGoalState_401_, 10);
v_extThms_418_ = lean_ctor_get(v_toGoalState_401_, 11);
v_ematch_419_ = lean_ctor_get(v_toGoalState_401_, 12);
v_inj_420_ = lean_ctor_get(v_toGoalState_401_, 13);
v_split_421_ = lean_ctor_get(v_toGoalState_401_, 14);
v_clean_422_ = lean_ctor_get(v_toGoalState_401_, 15);
v_sstates_423_ = lean_ctor_get(v_toGoalState_401_, 16);
v_isSharedCheck_436_ = !lean_is_exclusive(v_toGoalState_401_);
if (v_isSharedCheck_436_ == 0)
{
v___x_425_ = v_toGoalState_401_;
v_isShared_426_ = v_isSharedCheck_436_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_sstates_423_);
lean_inc(v_clean_422_);
lean_inc(v_split_421_);
lean_inc(v_inj_420_);
lean_inc(v_ematch_419_);
lean_inc(v_extThms_418_);
lean_inc(v_facts_417_);
lean_inc(v_newRawFacts_416_);
lean_inc(v_nextIdx_415_);
lean_inc(v_newFacts_413_);
lean_inc(v_indicesFound_412_);
lean_inc(v_appMap_411_);
lean_inc(v_congrTable_410_);
lean_inc(v_parents_409_);
lean_inc(v_exprs_408_);
lean_inc(v_enodeMap_407_);
lean_inc(v_nextDeclIdx_406_);
lean_dec(v_toGoalState_401_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_436_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
lean_inc(v_head_395_);
v___x_427_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v_enodeMap_407_, v_congrTable_410_, v_head_395_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 4, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_nextDeclIdx_406_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_enodeMap_407_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_exprs_408_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_parents_409_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v_appMap_411_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_indicesFound_412_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_newFacts_413_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_nextIdx_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 9, v_newRawFacts_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 10, v_facts_417_);
lean_ctor_set(v_reuseFailAlloc_435_, 11, v_extThms_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 12, v_ematch_419_);
lean_ctor_set(v_reuseFailAlloc_435_, 13, v_inj_420_);
lean_ctor_set(v_reuseFailAlloc_435_, 14, v_split_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 15, v_clean_422_);
lean_ctor_set(v_reuseFailAlloc_435_, 16, v_sstates_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*17, v_inconsistent_414_);
v___x_429_ = v_reuseFailAlloc_435_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_431_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_429_);
v___x_431_ = v___x_404_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_mvarId_402_);
v___x_431_ = v_reuseFailAlloc_434_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; 
v___x_432_ = lean_st_ref_put(v___y_399_, v___x_431_);
v_as_x27_381_ = v_tail_396_;
v_b_382_ = v___x_397_;
goto _start;
}
}
}
}
}
v___jp_438_:
{
if (v_a_439_ == 0)
{
v_as_x27_381_ = v_tail_396_;
v_b_382_ = v___x_397_;
goto _start;
}
else
{
lean_object* v_toCold_441_; lean_object* v_options_442_; uint8_t v_hasTrace_443_; 
v_toCold_441_ = lean_ctor_get(v___y_391_, 0);
v_options_442_ = lean_ctor_get(v_toCold_441_, 2);
v_hasTrace_443_ = lean_ctor_get_uint8(v_options_442_, sizeof(void*)*1);
if (v_hasTrace_443_ == 0)
{
v___y_399_ = v___y_383_;
goto v___jp_398_;
}
else
{
lean_object* v_inheritedTraceOptions_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_inheritedTraceOptions_444_ = lean_ctor_get(v_toCold_441_, 11);
v___x_445_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_446_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_447_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_444_, v_options_442_, v___x_446_);
if (v___x_447_ == 0)
{
v___y_399_ = v___y_383_;
goto v___jp_398_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_Grind_updateLastTag(v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec_ref_known(v___x_448_, 1);
v___x_449_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_395_);
v___x_450_ = l_Lean_MessageData_ofExpr(v_head_395_);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_445_, v___x_451_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_dec_ref_known(v___x_452_, 1);
v___y_399_ = v___y_383_;
goto v___jp_398_;
}
else
{
return v___x_452_;
}
}
else
{
return v___x_448_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_465_, v_b_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec(v___y_467_);
lean_dec(v_as_x27_465_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Meta_Grind_getParents___redArg(v_root_479_, v_a_480_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v___x_493_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_492_);
v___x_494_ = lean_box(0);
v___x_495_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_493_, v___x_494_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec(v___x_493_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v___x_495_, 0);
lean_dec(v_unused_503_);
v___x_497_ = v___x_495_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_dec(v___x_495_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v_a_492_);
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_492_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec(v_a_492_);
v_a_504_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_495_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_495_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_root_512_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_525_, lean_object* v_00_u03b2_526_, lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_525_, v_x_527_, v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_530_, lean_object* v_00_u03b2_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_530_, v_00_u03b2_531_, v_x_532_, v_x_533_);
lean_dec_ref(v___x_530_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_535_, lean_object* v_msg_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_535_, v_msg_536_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_549_, lean_object* v_msg_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_549_, v_msg_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec(v___y_551_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_563_, lean_object* v_as_x27_564_, lean_object* v_b_565_, lean_object* v_a_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_564_, v_b_565_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_579_, lean_object* v_as_x27_580_, lean_object* v_b_581_, lean_object* v_a_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_579_, v_as_x27_580_, v_b_581_, v_a_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec(v___y_583_);
lean_dec(v_as_x27_580_);
lean_dec(v_as_579_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_595_, lean_object* v_00_u03b2_596_, lean_object* v_x_597_, size_t v_x_598_, lean_object* v_x_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_595_, v_x_597_, v_x_598_, v_x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_601_, lean_object* v_00_u03b2_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
size_t v_x_23095__boxed_606_; lean_object* v_res_607_; 
v_x_23095__boxed_606_ = lean_unbox_usize(v_x_604_);
lean_dec(v_x_604_);
v_res_607_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_601_, v_00_u03b2_602_, v_x_603_, v_x_23095__boxed_606_, v_x_605_);
lean_dec_ref(v___x_601_);
return v_res_607_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_610_ = l_Lean_stringToMessageData(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_611_, lean_object* v_b_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
if (lean_obj_tag(v_as_x27_611_) == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_b_612_);
return v___x_624_;
}
else
{
lean_object* v_head_625_; lean_object* v_tail_626_; lean_object* v___x_627_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; uint8_t v_a_642_; uint8_t v___x_656_; 
v_head_625_ = lean_ctor_get(v_as_x27_611_, 0);
v_tail_626_ = lean_ctor_get(v_as_x27_611_, 1);
v___x_627_ = lean_box(0);
v___x_656_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_625_);
if (v___x_656_ == 0)
{
v_a_642_ = v___x_656_;
goto v___jp_641_;
}
else
{
lean_object* v___x_657_; 
lean_inc(v_head_625_);
v___x_657_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_625_, v___y_613_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; uint8_t v___x_659_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = lean_unbox(v_a_658_);
lean_dec(v_a_658_);
v_a_642_ = v___x_659_;
goto v___jp_641_;
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_a_660_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_657_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_657_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
v___jp_628_:
{
lean_object* v___x_639_; 
lean_inc(v_head_625_);
v___x_639_ = l_Lean_Meta_Grind_addCongrTable(v_head_625_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec_ref_known(v___x_639_, 1);
v_as_x27_611_ = v_tail_626_;
v_b_612_ = v___x_627_;
goto _start;
}
else
{
return v___x_639_;
}
}
v___jp_641_:
{
if (v_a_642_ == 0)
{
v_as_x27_611_ = v_tail_626_;
v_b_612_ = v___x_627_;
goto _start;
}
else
{
lean_object* v_toCold_644_; lean_object* v_options_645_; uint8_t v_hasTrace_646_; 
v_toCold_644_ = lean_ctor_get(v___y_621_, 0);
v_options_645_ = lean_ctor_get(v_toCold_644_, 2);
v_hasTrace_646_ = lean_ctor_get_uint8(v_options_645_, sizeof(void*)*1);
if (v_hasTrace_646_ == 0)
{
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
goto v___jp_628_;
}
else
{
lean_object* v_inheritedTraceOptions_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_inheritedTraceOptions_647_ = lean_ctor_get(v_toCold_644_, 11);
v___x_648_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_649_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_650_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_647_, v_options_645_, v___x_649_);
if (v___x_650_ == 0)
{
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
goto v___jp_628_;
}
else
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Grind_updateLastTag(v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec_ref_known(v___x_651_, 1);
v___x_652_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_625_);
v___x_653_ = l_Lean_MessageData_ofExpr(v_head_625_);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_648_, v___x_654_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_dec_ref_known(v___x_655_, 1);
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
v___y_637_ = v___y_621_;
v___y_638_ = v___y_622_;
goto v___jp_628_;
}
else
{
return v___x_655_;
}
}
else
{
return v___x_651_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_668_, lean_object* v_b_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_668_, v_b_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec(v___y_670_);
lean_dec(v_as_x27_668_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_682_);
v___x_695_ = lean_box(0);
v___x_696_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_694_, v___x_695_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
lean_dec(v___x_694_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v___x_696_, 0);
lean_dec(v_unused_704_);
v___x_698_ = v___x_696_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_dec(v___x_696_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_695_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_695_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec(v_a_706_);
lean_dec(v_parents_705_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_718_, lean_object* v_as_x27_719_, lean_object* v_b_720_, lean_object* v_a_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_719_, v_b_720_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_734_, lean_object* v_as_x27_735_, lean_object* v_b_736_, lean_object* v_a_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_734_, v_as_x27_735_, v_b_736_, v_a_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v_as_x27_735_);
lean_dec(v_as_734_);
return v_res_749_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_750_, lean_object* v_i_751_, lean_object* v_k_752_){
_start:
{
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = lean_array_get_size(v_keys_750_);
v___x_754_ = lean_nat_dec_lt(v_i_751_, v___x_753_);
if (v___x_754_ == 0)
{
lean_dec(v_i_751_);
return v___x_754_;
}
else
{
lean_object* v_k_x27_755_; uint8_t v___x_756_; 
v_k_x27_755_ = lean_array_fget_borrowed(v_keys_750_, v_i_751_);
v___x_756_ = l_Lean_instBEqMVarId_beq(v_k_752_, v_k_x27_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = lean_nat_add(v_i_751_, v___x_757_);
lean_dec(v_i_751_);
v_i_751_ = v___x_758_;
goto _start;
}
else
{
lean_dec(v_i_751_);
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_760_, lean_object* v_i_761_, lean_object* v_k_762_){
_start:
{
uint8_t v_res_763_; lean_object* v_r_764_; 
v_res_763_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_760_, v_i_761_, v_k_762_);
lean_dec(v_k_762_);
lean_dec_ref(v_keys_760_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_765_, size_t v_x_766_, lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
lean_object* v_es_768_; lean_object* v___x_769_; size_t v___x_770_; size_t v___x_771_; lean_object* v_j_772_; lean_object* v___x_773_; 
v_es_768_ = lean_ctor_get(v_x_765_, 0);
v___x_769_ = lean_box(2);
v___x_770_ = ((size_t)31ULL);
v___x_771_ = lean_usize_land(v_x_766_, v___x_770_);
v_j_772_ = lean_usize_to_nat(v___x_771_);
v___x_773_ = lean_array_get_borrowed(v___x_769_, v_es_768_, v_j_772_);
lean_dec(v_j_772_);
switch(lean_obj_tag(v___x_773_))
{
case 0:
{
lean_object* v_key_774_; uint8_t v___x_775_; 
v_key_774_ = lean_ctor_get(v___x_773_, 0);
v___x_775_ = l_Lean_instBEqMVarId_beq(v_x_767_, v_key_774_);
return v___x_775_;
}
case 1:
{
lean_object* v_node_776_; size_t v___x_777_; size_t v___x_778_; 
v_node_776_ = lean_ctor_get(v___x_773_, 0);
v___x_777_ = ((size_t)5ULL);
v___x_778_ = lean_usize_shift_right(v_x_766_, v___x_777_);
v_x_765_ = v_node_776_;
v_x_766_ = v___x_778_;
goto _start;
}
default: 
{
uint8_t v___x_780_; 
v___x_780_ = 0;
return v___x_780_;
}
}
}
else
{
lean_object* v_ks_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_ks_781_ = lean_ctor_get(v_x_765_, 0);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_781_, v___x_782_, v_x_767_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
size_t v_x_9681__boxed_787_; uint8_t v_res_788_; lean_object* v_r_789_; 
v_x_9681__boxed_787_ = lean_unbox_usize(v_x_785_);
lean_dec(v_x_785_);
v_res_788_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_784_, v_x_9681__boxed_787_, v_x_786_);
lean_dec(v_x_786_);
lean_dec_ref(v_x_784_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
uint64_t v___x_792_; size_t v___x_793_; uint8_t v___x_794_; 
v___x_792_ = l_Lean_instHashableMVarId_hash(v_x_791_);
v___x_793_ = lean_uint64_to_usize(v___x_792_);
v___x_794_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_790_, v___x_793_, v_x_791_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
uint8_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_795_, v_x_796_);
lean_dec(v_x_796_);
lean_dec_ref(v_x_795_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; lean_object* v_mctx_803_; lean_object* v_eAssignment_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_802_ = lean_st_ref_get(v___y_800_);
v_mctx_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc_ref(v_mctx_803_);
lean_dec(v___x_802_);
v_eAssignment_804_ = lean_ctor_get(v_mctx_803_, 8);
lean_inc_ref(v_eAssignment_804_);
lean_dec_ref(v_mctx_803_);
v___x_805_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_804_, v_mvarId_799_);
lean_dec_ref(v_eAssignment_804_);
v___x_806_ = lean_box(v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec(v_mvarId_808_);
return v_res_811_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_822_ = l_Lean_mkConst(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_830_ = l_Lean_mkConst(v___x_829_, v___x_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; lean_object* v_mvarId_843_; lean_object* v___x_844_; lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_898_; 
v___x_842_ = lean_st_ref_get(v_a_831_);
v_mvarId_843_ = lean_ctor_get(v___x_842_, 1);
lean_inc(v_mvarId_843_);
lean_dec(v___x_842_);
v___x_844_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_843_, v_a_838_);
lean_dec(v_mvarId_843_);
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_898_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_898_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_898_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
uint8_t v___x_849_; 
v___x_849_ = lean_unbox(v_a_845_);
lean_dec(v_a_845_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_del_object(v___x_847_);
v___x_850_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_835_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_851_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_835_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_835_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v___x_858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_860_ = l_Lean_mkApp4(v___x_858_, v_a_855_, v_a_857_, v_a_853_, v___x_859_);
v___x_861_ = l_Lean_Meta_Grind_closeGoal(v___x_860_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_861_;
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_a_855_);
lean_dec(v_a_853_);
v_a_862_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_856_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_856_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_a_853_);
v_a_870_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_854_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_854_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_a_878_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_852_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_852_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v_a_886_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_850_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_850_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = lean_box(0);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_894_);
v___x_896_ = v___x_847_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec(v_a_899_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_911_, v___y_919_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec(v___y_925_);
lean_dec(v_mvarId_924_);
return v_res_936_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_938_, v_x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
uint8_t v_res_944_; lean_object* v_r_945_; 
v_res_944_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_941_, v_x_942_, v_x_943_);
lean_dec(v_x_943_);
lean_dec_ref(v_x_942_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_946_, lean_object* v_x_947_, size_t v_x_948_, lean_object* v_x_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_947_, v_x_948_, v_x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_951_, lean_object* v_x_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
size_t v_x_9964__boxed_955_; uint8_t v_res_956_; lean_object* v_r_957_; 
v_x_9964__boxed_955_ = lean_unbox_usize(v_x_953_);
lean_dec(v_x_953_);
v_res_956_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_951_, v_x_952_, v_x_9964__boxed_955_, v_x_954_);
lean_dec(v_x_954_);
lean_dec_ref(v_x_952_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_958_, lean_object* v_keys_959_, lean_object* v_vals_960_, lean_object* v_heq_961_, lean_object* v_i_962_, lean_object* v_k_963_){
_start:
{
uint8_t v___x_964_; 
v___x_964_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_959_, v_i_962_, v_k_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_965_, lean_object* v_keys_966_, lean_object* v_vals_967_, lean_object* v_heq_968_, lean_object* v_i_969_, lean_object* v_k_970_){
_start:
{
uint8_t v_res_971_; lean_object* v_r_972_; 
v_res_971_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_965_, v_keys_966_, v_vals_967_, v_heq_968_, v_i_969_, v_k_970_);
lean_dec(v_k_970_);
lean_dec_ref(v_vals_967_);
lean_dec_ref(v_keys_966_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_box(0);
v___x_977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_978_ = l_Lean_mkConst(v___x_977_, v___x_976_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_979_, lean_object* v_rhs_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; 
lean_inc_ref(v_rhs_980_);
lean_inc_ref(v_lhs_979_);
v___x_992_ = l_Lean_Meta_mkEq(v_lhs_979_, v_rhs_980_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
lean_inc(v_a_990_);
lean_inc_ref(v_a_989_);
lean_inc(v_a_988_);
lean_inc_ref(v_a_987_);
lean_inc(v_a_986_);
lean_inc_ref(v_a_985_);
lean_inc(v_a_984_);
lean_inc_ref(v_a_983_);
lean_inc(v_a_982_);
lean_inc(v_a_981_);
v___x_994_ = lean_grind_mk_eq_proof(v_lhs_979_, v_rhs_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
lean_inc(v_a_993_);
v___x_996_ = l_Lean_Meta_mkDecide(v_a_993_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_999_ = l_Lean_Expr_appArg_x21(v_a_997_);
lean_dec(v_a_997_);
v___x_1000_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_993_);
v___x_1001_ = l_Lean_mkApp3(v___x_998_, v_a_993_, v___x_999_, v___x_1000_);
v___x_1002_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_985_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1005_ = l_Lean_mkApp4(v___x_1004_, v_a_993_, v_a_1003_, v___x_1001_, v_a_995_);
v___x_1006_ = l_Lean_Meta_Grind_closeGoal(v___x_1005_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
return v___x_1006_;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v___x_1001_);
lean_dec(v_a_995_);
lean_dec(v_a_993_);
v_a_1007_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1002_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1002_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_a_995_);
lean_dec(v_a_993_);
v_a_1015_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_996_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_996_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_a_993_);
v_a_1023_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_994_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_994_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v_rhs_980_);
lean_dec_ref(v_lhs_979_);
v_a_1031_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_992_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_992_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1039_, lean_object* v_rhs_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1039_, v_rhs_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec(v_a_1041_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1053_, lean_object* v_as_x27_1054_, lean_object* v_b_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
if (lean_obj_tag(v_as_x27_1054_) == 0)
{
lean_object* v___x_1067_; 
lean_dec(v___x_1053_);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_b_1055_);
return v___x_1067_;
}
else
{
lean_object* v_head_1068_; lean_object* v_tail_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_head_1068_ = lean_ctor_get(v_as_x27_1054_, 0);
v_tail_1069_ = lean_ctor_get(v_as_x27_1054_, 1);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_st_ref_get(v___y_1056_);
lean_inc(v_head_1068_);
v___x_1072_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1071_, v_head_1068_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___x_1071_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v_self_1074_; lean_object* v_next_1075_; lean_object* v_root_1076_; lean_object* v_congr_1077_; lean_object* v_target_x3f_1078_; lean_object* v_proof_x3f_1079_; uint8_t v_flipped_1080_; lean_object* v_size_1081_; uint8_t v_interpreted_1082_; uint8_t v_ctor_1083_; uint8_t v_hasLambdas_1084_; uint8_t v_heqProofs_1085_; lean_object* v_idx_1086_; lean_object* v_generation_1087_; lean_object* v_mt_1088_; lean_object* v_sTerms_1089_; uint8_t v_funCC_1090_; lean_object* v_ematchDiagSource_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1103_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v_self_1074_ = lean_ctor_get(v_a_1073_, 0);
v_next_1075_ = lean_ctor_get(v_a_1073_, 1);
v_root_1076_ = lean_ctor_get(v_a_1073_, 2);
v_congr_1077_ = lean_ctor_get(v_a_1073_, 3);
v_target_x3f_1078_ = lean_ctor_get(v_a_1073_, 4);
v_proof_x3f_1079_ = lean_ctor_get(v_a_1073_, 5);
v_flipped_1080_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*12);
v_size_1081_ = lean_ctor_get(v_a_1073_, 6);
v_interpreted_1082_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*12 + 1);
v_ctor_1083_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*12 + 2);
v_hasLambdas_1084_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*12 + 3);
v_heqProofs_1085_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*12 + 4);
v_idx_1086_ = lean_ctor_get(v_a_1073_, 7);
v_generation_1087_ = lean_ctor_get(v_a_1073_, 8);
v_mt_1088_ = lean_ctor_get(v_a_1073_, 9);
v_sTerms_1089_ = lean_ctor_get(v_a_1073_, 10);
v_funCC_1090_ = lean_ctor_get_uint8(v_a_1073_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1091_ = lean_ctor_get(v_a_1073_, 11);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_a_1073_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1093_ = v_a_1073_;
v_isShared_1094_ = v_isSharedCheck_1103_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_ematchDiagSource_1091_);
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
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1103_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_nat_dec_lt(v_mt_1088_, v___x_1053_);
lean_dec(v_mt_1088_);
if (v___x_1095_ == 0)
{
lean_del_object(v___x_1093_);
lean_dec(v_ematchDiagSource_1091_);
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
v_as_x27_1054_ = v_tail_1069_;
v_b_1055_ = v___x_1070_;
goto _start;
}
else
{
lean_object* v___x_1098_; 
lean_inc(v___x_1053_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 9, v___x_1053_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_self_1074_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_next_1075_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_root_1076_);
lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_congr_1077_);
lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_target_x3f_1078_);
lean_ctor_set(v_reuseFailAlloc_1102_, 5, v_proof_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1102_, 6, v_size_1081_);
lean_ctor_set(v_reuseFailAlloc_1102_, 7, v_idx_1086_);
lean_ctor_set(v_reuseFailAlloc_1102_, 8, v_generation_1087_);
lean_ctor_set(v_reuseFailAlloc_1102_, 9, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1102_, 10, v_sTerms_1089_);
lean_ctor_set(v_reuseFailAlloc_1102_, 11, v_ematchDiagSource_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*12, v_flipped_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*12 + 1, v_interpreted_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*12 + 2, v_ctor_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*12 + 3, v_hasLambdas_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*12 + 4, v_heqProofs_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*12 + 5, v_funCC_1090_);
v___x_1098_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; 
lean_inc(v_head_1068_);
v___x_1099_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1068_, v___x_1098_, v___y_1056_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref_known(v___x_1099_, 1);
v___x_1100_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1068_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_dec_ref_known(v___x_1100_, 1);
v_as_x27_1054_ = v_tail_1069_;
v_b_1055_ = v___x_1070_;
goto _start;
}
else
{
lean_dec(v___x_1053_);
return v___x_1100_;
}
}
else
{
lean_dec(v___x_1053_);
return v___x_1099_;
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v___x_1053_);
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
lean_object* v___x_1124_; lean_object* v_toGoalState_1125_; lean_object* v_ematch_1126_; lean_object* v_gmt_1127_; lean_object* v___x_1128_; 
v___x_1124_ = lean_st_ref_get(v_a_1113_);
v_toGoalState_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc_ref(v_toGoalState_1125_);
lean_dec(v___x_1124_);
v_ematch_1126_ = lean_ctor_get(v_toGoalState_1125_, 12);
lean_inc_ref(v_ematch_1126_);
lean_dec_ref(v_toGoalState_1125_);
v_gmt_1127_ = lean_ctor_get(v_ematch_1126_, 1);
lean_inc(v_gmt_1127_);
lean_dec_ref(v_ematch_1126_);
v___x_1128_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1129_);
lean_dec(v_a_1129_);
v___x_1131_ = lean_box(0);
v___x_1132_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1127_, v___x_1130_, v___x_1131_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
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
lean_dec(v_gmt_1127_);
v_a_1141_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1128_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1128_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1225_, lean_object* v_a_1226_, lean_object* v_fst_1227_, lean_object* v_a_1228_, lean_object* v_lams_1229_, lean_object* v_____r_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1225_, v_a_1228_, v___y_1231_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; uint8_t v___x_1281_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = lean_unbox(v_a_1280_);
lean_dec(v_a_1280_);
if (v___x_1281_ == 0)
{
goto v___jp_1242_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_inc(v_fst_1227_);
v___x_1282_ = l_Array_reverse___redArg(v_fst_1227_);
lean_inc(v_snd_1225_);
v___x_1283_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1229_, v_snd_1225_, v___x_1282_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_dec_ref_known(v___x_1283_, 1);
goto v___jp_1242_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_fst_1227_);
lean_dec(v_snd_1225_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_fst_1227_);
lean_dec(v_snd_1225_);
v_a_1292_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1279_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1279_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
v___jp_1242_:
{
if (lean_obj_tag(v_snd_1225_) == 5)
{
lean_object* v_fn_1243_; lean_object* v_arg_1244_; lean_object* v___x_1245_; 
v_fn_1243_ = lean_ctor_get(v_snd_1225_, 0);
lean_inc_ref(v_fn_1243_);
v_arg_1244_ = lean_ctor_get(v_snd_1225_, 1);
lean_inc_ref(v_arg_1244_);
v___x_1245_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1226_, v___y_1231_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v___x_1247_ = lean_box(0);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
lean_inc(v___y_1236_);
lean_inc_ref(v___y_1235_);
lean_inc(v___y_1234_);
lean_inc_ref(v___y_1233_);
lean_inc(v___y_1232_);
lean_inc(v___y_1231_);
v___x_1248_ = lean_grind_internalize(v_snd_1225_, v_a_1246_, v___x_1247_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1258_; 
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1248_, 0);
lean_dec(v_unused_1259_);
v___x_1250_ = v___x_1248_;
v_isShared_1251_ = v_isSharedCheck_1258_;
goto v_resetjp_1249_;
}
else
{
lean_dec(v___x_1248_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1258_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1252_ = lean_array_push(v_fst_1227_, v_arg_1244_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v_fn_1243_);
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1254_);
v___x_1256_ = v___x_1250_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_arg_1244_);
lean_dec_ref(v_fn_1243_);
lean_dec(v_fst_1227_);
v_a_1260_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1248_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1248_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_arg_1244_);
lean_dec_ref_known(v_snd_1225_, 2);
lean_dec_ref(v_fn_1243_);
lean_dec(v_fst_1227_);
v_a_1268_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1245_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1245_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_fst_1227_);
lean_ctor_set(v___x_1276_, 1, v_snd_1225_);
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1300_ = _args[0];
lean_object* v_a_1301_ = _args[1];
lean_object* v_fst_1302_ = _args[2];
lean_object* v_a_1303_ = _args[3];
lean_object* v_lams_1304_ = _args[4];
lean_object* v_____r_1305_ = _args[5];
lean_object* v___y_1306_ = _args[6];
lean_object* v___y_1307_ = _args[7];
lean_object* v___y_1308_ = _args[8];
lean_object* v___y_1309_ = _args[9];
lean_object* v___y_1310_ = _args[10];
lean_object* v___y_1311_ = _args[11];
lean_object* v___y_1312_ = _args[12];
lean_object* v___y_1313_ = _args[13];
lean_object* v___y_1314_ = _args[14];
lean_object* v___y_1315_ = _args[15];
lean_object* v___y_1316_ = _args[16];
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1300_, v_a_1301_, v_fst_1302_, v_a_1303_, v_lams_1304_, v_____r_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v_lams_1304_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_a_1301_);
return v_res_1317_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1324_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1325_ = l_Lean_Name_append(v___x_1324_, v___x_1323_);
return v___x_1325_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_lams_1331_, lean_object* v_a_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___y_1345_; lean_object* v_toCold_1365_; lean_object* v_options_1366_; lean_object* v_fst_1367_; lean_object* v_snd_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1405_; 
v_toCold_1365_ = lean_ctor_get(v___y_1341_, 0);
v_options_1366_ = lean_ctor_get(v_toCold_1365_, 2);
v_fst_1367_ = lean_ctor_get(v_a_1332_, 0);
v_snd_1368_ = lean_ctor_get(v_a_1332_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_a_1332_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1370_ = v_a_1332_;
v_isShared_1371_ = v_isSharedCheck_1405_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_snd_1368_);
lean_inc(v_fst_1367_);
lean_dec(v_a_1332_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1405_;
goto v_resetjp_1369_;
}
v___jp_1344_:
{
if (lean_obj_tag(v___y_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1356_; 
v_a_1346_ = lean_ctor_get(v___y_1345_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___y_1345_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1348_ = v___y_1345_;
v_isShared_1349_ = v_isSharedCheck_1356_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___y_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1356_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
if (lean_obj_tag(v_a_1346_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v_a_1346_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v_a_1346_, 1);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v_a_1350_);
v___x_1352_ = v___x_1348_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
else
{
lean_object* v_a_1354_; 
lean_del_object(v___x_1348_);
v_a_1354_ = lean_ctor_get(v_a_1346_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v_a_1346_, 1);
v_a_1332_ = v_a_1354_;
goto _start;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_a_1357_ = lean_ctor_get(v___y_1345_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___y_1345_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___y_1345_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___y_1345_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
v_resetjp_1369_:
{
lean_object* v_inheritedTraceOptions_1372_; uint8_t v_hasTrace_1373_; 
v_inheritedTraceOptions_1372_ = lean_ctor_get(v_toCold_1365_, 11);
v_hasTrace_1373_ = lean_ctor_get_uint8(v_options_1366_, sizeof(void*)*1);
if (v_hasTrace_1373_ == 0)
{
lean_del_object(v___x_1370_);
goto v___jp_1374_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1377_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1378_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1379_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1372_, v_options_1366_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_del_object(v___x_1370_);
goto v___jp_1374_;
}
else
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Meta_Grind_updateLastTag(v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
lean_dec_ref_known(v___x_1380_, 1);
v___x_1381_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1368_);
v___x_1382_ = l_Lean_MessageData_ofExpr(v_snd_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 7);
lean_ctor_set(v___x_1370_, 1, v___x_1382_);
lean_ctor_set(v___x_1370_, 0, v___x_1381_);
v___x_1384_ = v___x_1370_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1377_, v___x_1384_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1387_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1368_, v_a_1329_, v_fst_1367_, v_a_1330_, v_lams_1331_, v_a_1386_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
v___y_1345_ = v___x_1387_;
goto v___jp_1344_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_snd_1368_);
lean_dec(v_fst_1367_);
v_a_1388_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1385_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1385_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_del_object(v___x_1370_);
lean_dec(v_snd_1368_);
lean_dec(v_fst_1367_);
v_a_1397_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1380_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1380_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
v___jp_1374_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1368_, v_a_1329_, v_fst_1367_, v_a_1330_, v_lams_1331_, v___x_1375_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
v___y_1345_ = v___x_1376_;
goto v___jp_1344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_lams_1408_, lean_object* v_a_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1406_, v_a_1407_, v_lams_1408_, v_a_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v_lams_1408_);
lean_dec_ref(v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1421_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1426_ = l_Lean_stringToMessageData(v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1427_, lean_object* v_lams_1428_, lean_object* v_as_x27_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
if (lean_obj_tag(v_as_x27_1429_) == 0)
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_b_1430_);
return v___x_1442_;
}
else
{
lean_object* v_toCold_1443_; lean_object* v_options_1444_; lean_object* v_head_1445_; lean_object* v_tail_1446_; lean_object* v_inheritedTraceOptions_1447_; uint8_t v_hasTrace_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; 
v_toCold_1443_ = lean_ctor_get(v___y_1439_, 0);
v_options_1444_ = lean_ctor_get(v_toCold_1443_, 2);
v_head_1445_ = lean_ctor_get(v_as_x27_1429_, 0);
v_tail_1446_ = lean_ctor_get(v_as_x27_1429_, 1);
v_inheritedTraceOptions_1447_ = lean_ctor_get(v_toCold_1443_, 11);
v_hasTrace_1448_ = lean_ctor_get_uint8(v_options_1444_, sizeof(void*)*1);
v___x_1449_ = lean_box(0);
v___x_1450_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1448_ == 0)
{
v___y_1452_ = v___y_1431_;
v___y_1453_ = v___y_1432_;
v___y_1454_ = v___y_1433_;
v___y_1455_ = v___y_1434_;
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1474_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1475_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1447_, v_options_1444_, v___x_1474_);
if (v___x_1475_ == 0)
{
v___y_1452_ = v___y_1431_;
v___y_1453_ = v___y_1432_;
v___y_1454_ = v___y_1433_;
v___y_1455_ = v___y_1434_;
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Meta_Grind_updateLastTag(v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec_ref_known(v___x_1476_, 1);
v___x_1477_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1445_);
v___x_1478_ = l_Lean_MessageData_ofExpr(v_head_1445_);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1473_, v___x_1479_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_dec_ref_known(v___x_1480_, 1);
v___y_1452_ = v___y_1431_;
v___y_1453_ = v___y_1432_;
v___y_1454_ = v___y_1433_;
v___y_1455_ = v___y_1434_;
v___y_1456_ = v___y_1435_;
v___y_1457_ = v___y_1436_;
v___y_1458_ = v___y_1437_;
v___y_1459_ = v___y_1438_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
goto v___jp_1451_;
}
else
{
return v___x_1480_;
}
}
else
{
return v___x_1476_;
}
}
}
v___jp_1451_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_inc(v_head_1445_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1450_);
lean_ctor_set(v___x_1462_, 1, v_head_1445_);
v___x_1463_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1445_, v_a_1427_, v_lams_1428_, v___x_1462_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_dec_ref_known(v___x_1463_, 1);
v_as_x27_1429_ = v_tail_1446_;
v_b_1430_ = v___x_1449_;
goto _start;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_a_1465_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1463_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1481_, lean_object* v_lams_1482_, lean_object* v_as_x27_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1481_, v_lams_1482_, v_as_x27_1483_, v_b_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec(v_as_x27_1483_);
lean_dec_ref(v_lams_1482_);
lean_dec_ref(v_a_1481_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1497_, lean_object* v_lams_1498_, lean_object* v_as_1499_, lean_object* v_as_x27_1500_, lean_object* v_b_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
if (lean_obj_tag(v_as_x27_1500_) == 0)
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_b_1501_);
return v___x_1513_;
}
else
{
lean_object* v_toCold_1514_; lean_object* v_options_1515_; lean_object* v_head_1516_; lean_object* v_tail_1517_; lean_object* v_inheritedTraceOptions_1518_; uint8_t v_hasTrace_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; 
v_toCold_1514_ = lean_ctor_get(v___y_1510_, 0);
v_options_1515_ = lean_ctor_get(v_toCold_1514_, 2);
v_head_1516_ = lean_ctor_get(v_as_x27_1500_, 0);
v_tail_1517_ = lean_ctor_get(v_as_x27_1500_, 1);
v_inheritedTraceOptions_1518_ = lean_ctor_get(v_toCold_1514_, 11);
v_hasTrace_1519_ = lean_ctor_get_uint8(v_options_1515_, sizeof(void*)*1);
v___x_1520_ = lean_box(0);
v___x_1521_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_hasTrace_1519_ == 0)
{
v___y_1523_ = v___y_1502_;
v___y_1524_ = v___y_1503_;
v___y_1525_ = v___y_1504_;
v___y_1526_ = v___y_1505_;
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
goto v___jp_1522_;
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1544_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1545_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1546_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1518_, v_options_1515_, v___x_1545_);
if (v___x_1546_ == 0)
{
v___y_1523_ = v___y_1502_;
v___y_1524_ = v___y_1503_;
v___y_1525_ = v___y_1504_;
v___y_1526_ = v___y_1505_;
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
goto v___jp_1522_;
}
else
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Meta_Grind_updateLastTag(v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref_known(v___x_1547_, 1);
v___x_1548_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1516_);
v___x_1549_ = l_Lean_MessageData_ofExpr(v_head_1516_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1544_, v___x_1550_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_dec_ref_known(v___x_1551_, 1);
v___y_1523_ = v___y_1502_;
v___y_1524_ = v___y_1503_;
v___y_1525_ = v___y_1504_;
v___y_1526_ = v___y_1505_;
v___y_1527_ = v___y_1506_;
v___y_1528_ = v___y_1507_;
v___y_1529_ = v___y_1508_;
v___y_1530_ = v___y_1509_;
v___y_1531_ = v___y_1510_;
v___y_1532_ = v___y_1511_;
goto v___jp_1522_;
}
else
{
return v___x_1551_;
}
}
else
{
return v___x_1547_;
}
}
}
v___jp_1522_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_inc(v_head_1516_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1521_);
lean_ctor_set(v___x_1533_, 1, v_head_1516_);
v___x_1534_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1516_, v_a_1497_, v_lams_1498_, v___x_1533_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v___x_1535_; 
lean_dec_ref_known(v___x_1534_, 1);
v___x_1535_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1497_, v_lams_1498_, v_tail_1517_, v___x_1520_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
return v___x_1535_;
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_a_1536_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1534_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1534_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1552_, lean_object* v_lams_1553_, lean_object* v_as_1554_, lean_object* v_as_x27_1555_, lean_object* v_b_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1552_, v_lams_1553_, v_as_1554_, v_as_x27_1555_, v_b_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec(v_as_x27_1555_);
lean_dec(v_as_1554_);
lean_dec_ref(v_lams_1553_);
lean_dec_ref(v_a_1552_);
return v_res_1568_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1571_ = l_Lean_stringToMessageData(v___x_1570_);
return v___x_1571_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1575_, lean_object* v_lams_1576_, lean_object* v_as_1577_, size_t v_sz_1578_, size_t v_i_1579_, lean_object* v_b_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_usize_dec_lt(v_i_1579_, v_sz_1578_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v_b_1580_);
return v___x_1593_;
}
else
{
lean_object* v_toCold_1594_; lean_object* v_options_1595_; lean_object* v_inheritedTraceOptions_1596_; uint8_t v_hasTrace_1597_; lean_object* v___x_1598_; lean_object* v_a_1599_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; 
v_toCold_1594_ = lean_ctor_get(v___y_1589_, 0);
v_options_1595_ = lean_ctor_get(v_toCold_1594_, 2);
v_inheritedTraceOptions_1596_ = lean_ctor_get(v_toCold_1594_, 11);
v_hasTrace_1597_ = lean_ctor_get_uint8(v_options_1595_, sizeof(void*)*1);
v___x_1598_ = lean_box(0);
v_a_1599_ = lean_array_uget_borrowed(v_as_1577_, v_i_1579_);
if (v_hasTrace_1597_ == 0)
{
v___y_1601_ = v___y_1581_;
v___y_1602_ = v___y_1582_;
v___y_1603_ = v___y_1583_;
v___y_1604_ = v___y_1584_;
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1626_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1627_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1628_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1596_, v_options_1595_, v___x_1627_);
if (v___x_1628_ == 0)
{
v___y_1601_ = v___y_1581_;
v___y_1602_ = v___y_1582_;
v___y_1603_ = v___y_1583_;
v___y_1604_ = v___y_1584_;
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
goto v___jp_1600_;
}
else
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Meta_Grind_updateLastTag(v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v___x_1630_; 
lean_dec_ref_known(v___x_1629_, 1);
v___x_1630_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1599_, v___y_1581_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1599_);
v___x_1633_ = l_Lean_MessageData_ofExpr(v_a_1599_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1631_);
lean_dec(v_a_1631_);
v___x_1638_ = lean_box(0);
v___x_1639_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1637_, v___x_1638_);
v___x_1640_ = l_Lean_MessageData_ofList(v___x_1639_);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1636_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1626_, v___x_1641_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_dec_ref_known(v___x_1642_, 1);
v___y_1601_ = v___y_1581_;
v___y_1602_ = v___y_1582_;
v___y_1603_ = v___y_1583_;
v___y_1604_ = v___y_1584_;
v___y_1605_ = v___y_1585_;
v___y_1606_ = v___y_1586_;
v___y_1607_ = v___y_1587_;
v___y_1608_ = v___y_1588_;
v___y_1609_ = v___y_1589_;
v___y_1610_ = v___y_1590_;
goto v___jp_1600_;
}
else
{
return v___x_1642_;
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1630_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1630_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
return v___x_1629_;
}
}
}
v___jp_1600_:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1599_, v___y_1601_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___x_1613_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1612_);
lean_dec(v_a_1612_);
v___x_1614_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1575_, v_lams_1576_, v___x_1613_, v___x_1613_, v___x_1598_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___x_1613_);
if (lean_obj_tag(v___x_1614_) == 0)
{
size_t v___x_1615_; size_t v___x_1616_; 
lean_dec_ref_known(v___x_1614_, 1);
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1579_, v___x_1615_);
v_i_1579_ = v___x_1616_;
v_b_1580_ = v___x_1598_;
goto _start;
}
else
{
return v___x_1614_;
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
v_a_1618_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1611_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1611_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___boxed(lean_object** _args){
lean_object* v_a_1651_ = _args[0];
lean_object* v_lams_1652_ = _args[1];
lean_object* v_as_1653_ = _args[2];
lean_object* v_sz_1654_ = _args[3];
lean_object* v_i_1655_ = _args[4];
lean_object* v_b_1656_ = _args[5];
lean_object* v___y_1657_ = _args[6];
lean_object* v___y_1658_ = _args[7];
lean_object* v___y_1659_ = _args[8];
lean_object* v___y_1660_ = _args[9];
lean_object* v___y_1661_ = _args[10];
lean_object* v___y_1662_ = _args[11];
lean_object* v___y_1663_ = _args[12];
lean_object* v___y_1664_ = _args[13];
lean_object* v___y_1665_ = _args[14];
lean_object* v___y_1666_ = _args[15];
lean_object* v___y_1667_ = _args[16];
_start:
{
size_t v_sz_boxed_1668_; size_t v_i_boxed_1669_; lean_object* v_res_1670_; 
v_sz_boxed_1668_ = lean_unbox_usize(v_sz_1654_);
lean_dec(v_sz_1654_);
v_i_boxed_1669_ = lean_unbox_usize(v_i_1655_);
lean_dec(v_i_1655_);
v_res_1670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1651_, v_lams_1652_, v_as_1653_, v_sz_boxed_1668_, v_i_boxed_1669_, v_b_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v_as_1653_);
lean_dec_ref(v_lams_1652_);
lean_dec_ref(v_a_1651_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(lean_object* v_a_1671_, lean_object* v_lams_1672_, lean_object* v_as_1673_, size_t v_sz_1674_, size_t v_i_1675_, lean_object* v_b_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_lt(v_i_1675_, v_sz_1674_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_b_1676_);
return v___x_1689_;
}
else
{
lean_object* v_toCold_1690_; lean_object* v_options_1691_; lean_object* v_inheritedTraceOptions_1692_; uint8_t v_hasTrace_1693_; lean_object* v___x_1694_; lean_object* v_a_1695_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; 
v_toCold_1690_ = lean_ctor_get(v___y_1685_, 0);
v_options_1691_ = lean_ctor_get(v_toCold_1690_, 2);
v_inheritedTraceOptions_1692_ = lean_ctor_get(v_toCold_1690_, 11);
v_hasTrace_1693_ = lean_ctor_get_uint8(v_options_1691_, sizeof(void*)*1);
v___x_1694_ = lean_box(0);
v_a_1695_ = lean_array_uget_borrowed(v_as_1673_, v_i_1675_);
if (v_hasTrace_1693_ == 0)
{
v___y_1697_ = v___y_1677_;
v___y_1698_ = v___y_1678_;
v___y_1699_ = v___y_1679_;
v___y_1700_ = v___y_1680_;
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1722_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1723_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1724_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1692_, v_options_1691_, v___x_1723_);
if (v___x_1724_ == 0)
{
v___y_1697_ = v___y_1677_;
v___y_1698_ = v___y_1678_;
v___y_1699_ = v___y_1679_;
v___y_1700_ = v___y_1680_;
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Meta_Grind_updateLastTag(v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v___x_1726_; 
lean_dec_ref_known(v___x_1725_, 1);
v___x_1726_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1695_, v___y_1677_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1);
lean_inc(v_a_1695_);
v___x_1729_ = l_Lean_MessageData_ofExpr(v_a_1695_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3);
v___x_1732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1727_);
lean_dec(v_a_1727_);
v___x_1734_ = lean_box(0);
v___x_1735_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1733_, v___x_1734_);
v___x_1736_ = l_Lean_MessageData_ofList(v___x_1735_);
v___x_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1732_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1722_, v___x_1737_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_dec_ref_known(v___x_1738_, 1);
v___y_1697_ = v___y_1677_;
v___y_1698_ = v___y_1678_;
v___y_1699_ = v___y_1679_;
v___y_1700_ = v___y_1680_;
v___y_1701_ = v___y_1681_;
v___y_1702_ = v___y_1682_;
v___y_1703_ = v___y_1683_;
v___y_1704_ = v___y_1684_;
v___y_1705_ = v___y_1685_;
v___y_1706_ = v___y_1686_;
goto v___jp_1696_;
}
else
{
return v___x_1738_;
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1726_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1726_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
return v___x_1725_;
}
}
}
v___jp_1696_:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1695_, v___y_1697_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1708_);
lean_dec(v_a_1708_);
v___x_1710_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1671_, v_lams_1672_, v___x_1709_, v___x_1709_, v___x_1694_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___x_1709_);
if (lean_obj_tag(v___x_1710_) == 0)
{
size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
lean_dec_ref_known(v___x_1710_, 1);
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1675_, v___x_1711_);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1671_, v_lams_1672_, v_as_1673_, v_sz_1674_, v___x_1712_, v___x_1694_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
return v___x_1713_;
}
else
{
return v___x_1710_;
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_a_1714_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1707_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1707_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3___boxed(lean_object** _args){
lean_object* v_a_1747_ = _args[0];
lean_object* v_lams_1748_ = _args[1];
lean_object* v_as_1749_ = _args[2];
lean_object* v_sz_1750_ = _args[3];
lean_object* v_i_1751_ = _args[4];
lean_object* v_b_1752_ = _args[5];
lean_object* v___y_1753_ = _args[6];
lean_object* v___y_1754_ = _args[7];
lean_object* v___y_1755_ = _args[8];
lean_object* v___y_1756_ = _args[9];
lean_object* v___y_1757_ = _args[10];
lean_object* v___y_1758_ = _args[11];
lean_object* v___y_1759_ = _args[12];
lean_object* v___y_1760_ = _args[13];
lean_object* v___y_1761_ = _args[14];
lean_object* v___y_1762_ = _args[15];
lean_object* v___y_1763_ = _args[16];
_start:
{
size_t v_sz_boxed_1764_; size_t v_i_boxed_1765_; lean_object* v_res_1766_; 
v_sz_boxed_1764_ = lean_unbox_usize(v_sz_1750_);
lean_dec(v_sz_1750_);
v_i_boxed_1765_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_res_1766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1747_, v_lams_1748_, v_as_1749_, v_sz_boxed_1764_, v_i_boxed_1765_, v_b_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v_as_1749_);
lean_dec_ref(v_lams_1748_);
lean_dec_ref(v_a_1747_);
return v_res_1766_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__1(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__0));
v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateBeta___closed__3(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBeta___closed__2));
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta(lean_object* v_lams_1773_, lean_object* v_fns_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1786_ = lean_array_get_size(v_lams_1773_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_nat_dec_eq(v___x_1786_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1789_ = l_Lean_instInhabitedExpr;
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = lean_nat_sub(v___x_1786_, v___x_1790_);
v___x_1792_ = lean_array_get_borrowed(v___x_1789_, v_lams_1773_, v___x_1791_);
lean_dec(v___x_1791_);
v___x_1793_ = lean_st_ref_get(v_a_1775_);
lean_inc(v___x_1792_);
v___x_1794_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1793_, v___x_1792_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
lean_dec(v___x_1793_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v_toCold_1819_; lean_object* v_options_1820_; uint8_t v_hasTrace_1821_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v_toCold_1819_ = lean_ctor_get(v_a_1783_, 0);
v_options_1820_ = lean_ctor_get(v_toCold_1819_, 2);
v_hasTrace_1821_ = lean_ctor_get_uint8(v_options_1820_, sizeof(void*)*1);
if (v_hasTrace_1821_ == 0)
{
v___y_1797_ = v_a_1775_;
v___y_1798_ = v_a_1776_;
v___y_1799_ = v_a_1777_;
v___y_1800_ = v_a_1778_;
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
goto v___jp_1796_;
}
else
{
lean_object* v_inheritedTraceOptions_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v_inheritedTraceOptions_1822_ = lean_ctor_get(v_toCold_1819_, 11);
v___x_1823_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1824_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1825_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1822_, v_options_1820_, v___x_1824_);
if (v___x_1825_ == 0)
{
v___y_1797_ = v_a_1775_;
v___y_1798_ = v_a_1776_;
v___y_1799_ = v_a_1777_;
v___y_1800_ = v_a_1778_;
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_Meta_Grind_updateLastTag(v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec_ref_known(v___x_1826_, 1);
v___x_1827_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1774_);
v___x_1828_ = lean_array_to_list(v_fns_1774_);
v___x_1829_ = lean_box(0);
v___x_1830_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1828_, v___x_1829_);
v___x_1831_ = l_Lean_MessageData_ofList(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1827_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
lean_inc_ref(v_lams_1773_);
v___x_1835_ = lean_array_to_list(v_lams_1773_);
v___x_1836_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1835_, v___x_1829_);
v___x_1837_ = l_Lean_MessageData_ofList(v___x_1836_);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1834_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1823_, v___x_1838_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_dec_ref_known(v___x_1839_, 1);
v___y_1797_ = v_a_1775_;
v___y_1798_ = v_a_1776_;
v___y_1799_ = v_a_1777_;
v___y_1800_ = v_a_1778_;
v___y_1801_ = v_a_1779_;
v___y_1802_ = v_a_1780_;
v___y_1803_ = v_a_1781_;
v___y_1804_ = v_a_1782_;
v___y_1805_ = v_a_1783_;
v___y_1806_ = v_a_1784_;
goto v___jp_1796_;
}
else
{
lean_dec(v_a_1795_);
lean_dec_ref(v_fns_1774_);
lean_dec_ref(v_lams_1773_);
return v___x_1839_;
}
}
else
{
lean_dec(v_a_1795_);
lean_dec_ref(v_fns_1774_);
lean_dec_ref(v_lams_1773_);
return v___x_1826_;
}
}
}
v___jp_1796_:
{
lean_object* v___x_1807_; size_t v_sz_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = lean_box(0);
v_sz_1808_ = lean_array_size(v_fns_1774_);
v___x_1809_ = ((size_t)0ULL);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3(v_a_1795_, v_lams_1773_, v_fns_1774_, v_sz_1808_, v___x_1809_, v___x_1807_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec_ref(v_fns_1774_);
lean_dec_ref(v_lams_1773_);
lean_dec(v_a_1795_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v___x_1810_, 0);
lean_dec(v_unused_1818_);
v___x_1812_ = v___x_1810_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_dec(v___x_1810_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1807_);
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1807_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
return v___x_1810_;
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec_ref(v_fns_1774_);
lean_dec_ref(v_lams_1773_);
v_a_1840_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1794_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1794_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec_ref(v_fns_1774_);
lean_dec_ref(v_lams_1773_);
v___x_1848_ = lean_box(0);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1850_, lean_object* v_fns_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1850_, v_fns_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec(v_a_1852_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_lams_1866_, lean_object* v_inst_1867_, lean_object* v_a_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1864_, v_a_1865_, v_lams_1866_, v_a_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_lams_1883_, lean_object* v_inst_1884_, lean_object* v_a_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1881_, v_a_1882_, v_lams_1883_, v_inst_1884_, v_a_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v_lams_1883_);
lean_dec_ref(v_a_1882_);
lean_dec_ref(v_a_1881_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1898_, lean_object* v_lams_1899_, lean_object* v_as_1900_, lean_object* v_as_x27_1901_, lean_object* v_b_1902_, lean_object* v_a_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1898_, v_lams_1899_, v_as_1900_, v_as_x27_1901_, v_b_1902_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1916_ = _args[0];
lean_object* v_lams_1917_ = _args[1];
lean_object* v_as_1918_ = _args[2];
lean_object* v_as_x27_1919_ = _args[3];
lean_object* v_b_1920_ = _args[4];
lean_object* v_a_1921_ = _args[5];
lean_object* v___y_1922_ = _args[6];
lean_object* v___y_1923_ = _args[7];
lean_object* v___y_1924_ = _args[8];
lean_object* v___y_1925_ = _args[9];
lean_object* v___y_1926_ = _args[10];
lean_object* v___y_1927_ = _args[11];
lean_object* v___y_1928_ = _args[12];
lean_object* v___y_1929_ = _args[13];
lean_object* v___y_1930_ = _args[14];
lean_object* v___y_1931_ = _args[15];
lean_object* v___y_1932_ = _args[16];
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1916_, v_lams_1917_, v_as_1918_, v_as_x27_1919_, v_b_1920_, v_a_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec(v_as_x27_1919_);
lean_dec(v_as_1918_);
lean_dec_ref(v_lams_1917_);
lean_dec_ref(v_a_1916_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1934_, lean_object* v_lams_1935_, lean_object* v_as_1936_, lean_object* v_as_x27_1937_, lean_object* v_b_1938_, lean_object* v_a_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1934_, v_lams_1935_, v_as_x27_1937_, v_b_1938_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1952_ = _args[0];
lean_object* v_lams_1953_ = _args[1];
lean_object* v_as_1954_ = _args[2];
lean_object* v_as_x27_1955_ = _args[3];
lean_object* v_b_1956_ = _args[4];
lean_object* v_a_1957_ = _args[5];
lean_object* v___y_1958_ = _args[6];
lean_object* v___y_1959_ = _args[7];
lean_object* v___y_1960_ = _args[8];
lean_object* v___y_1961_ = _args[9];
lean_object* v___y_1962_ = _args[10];
lean_object* v___y_1963_ = _args[11];
lean_object* v___y_1964_ = _args[12];
lean_object* v___y_1965_ = _args[13];
lean_object* v___y_1966_ = _args[14];
lean_object* v___y_1967_ = _args[15];
lean_object* v___y_1968_ = _args[16];
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1952_, v_lams_1953_, v_as_1954_, v_as_x27_1955_, v_b_1956_, v_a_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec(v_as_x27_1955_);
lean_dec(v_as_1954_);
lean_dec_ref(v_lams_1953_);
lean_dec_ref(v_a_1952_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1973_, lean_object* v_as_1974_, size_t v_sz_1975_, size_t v_i_1976_, lean_object* v_b_1977_){
_start:
{
lean_object* v_a_1979_; uint8_t v___x_1983_; 
v___x_1983_ = lean_usize_dec_lt(v_i_1976_, v_sz_1975_);
if (v___x_1983_ == 0)
{
lean_inc_ref(v_b_1977_);
return v_b_1977_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v_a_1986_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_1986_ = lean_array_uget_borrowed(v_as_1974_, v_i_1976_);
if (lean_obj_tag(v_a_1986_) == 6)
{
lean_object* v_binderType_1987_; size_t v___x_1988_; size_t v___x_1989_; uint8_t v___x_1990_; 
v_binderType_1987_ = lean_ctor_get(v_a_1986_, 1);
v___x_1988_ = lean_ptr_addr(v_d_1973_);
v___x_1989_ = lean_ptr_addr(v_binderType_1987_);
v___x_1990_ = lean_usize_dec_eq(v___x_1988_, v___x_1989_);
if (v___x_1990_ == 0)
{
v_a_1979_ = v___x_1985_;
goto v___jp_1978_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
lean_inc_ref(v_a_1986_);
v___x_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1991_, 0, v_a_1986_);
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
lean_ctor_set(v___x_1993_, 1, v___x_1984_);
return v___x_1993_;
}
}
else
{
v_a_1979_ = v___x_1985_;
goto v___jp_1978_;
}
}
v___jp_1978_:
{
size_t v___x_1980_; size_t v___x_1981_; 
v___x_1980_ = ((size_t)1ULL);
v___x_1981_ = lean_usize_add(v_i_1976_, v___x_1980_);
v_i_1976_ = v___x_1981_;
v_b_1977_ = v_a_1979_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_1994_, lean_object* v_as_1995_, lean_object* v_sz_1996_, lean_object* v_i_1997_, lean_object* v_b_1998_){
_start:
{
size_t v_sz_boxed_1999_; size_t v_i_boxed_2000_; lean_object* v_res_2001_; 
v_sz_boxed_1999_ = lean_unbox_usize(v_sz_1996_);
lean_dec(v_sz_1996_);
v_i_boxed_2000_ = lean_unbox_usize(v_i_1997_);
lean_dec(v_i_1997_);
v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_1994_, v_as_1995_, v_sz_boxed_1999_, v_i_boxed_2000_, v_b_1998_);
lean_dec_ref(v_b_1998_);
lean_dec_ref(v_as_1995_);
lean_dec_ref(v_d_1994_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2002_, lean_object* v_d_2003_){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; size_t v_sz_2006_; size_t v___x_2007_; lean_object* v___x_2008_; lean_object* v_fst_2009_; 
v___x_2004_ = lean_box(0);
v___x_2005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2006_ = lean_array_size(v_lams_2002_);
v___x_2007_ = ((size_t)0ULL);
v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2003_, v_lams_2002_, v_sz_2006_, v___x_2007_, v___x_2005_);
v_fst_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_fst_2009_);
lean_dec_ref(v___x_2008_);
if (lean_obj_tag(v_fst_2009_) == 0)
{
return v___x_2004_;
}
else
{
lean_object* v_val_2010_; 
v_val_2010_ = lean_ctor_get(v_fst_2009_, 0);
lean_inc(v_val_2010_);
lean_dec_ref_known(v_fst_2009_, 1);
return v_val_2010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2011_, lean_object* v_d_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2011_, v_d_2012_);
lean_dec_ref(v_d_2012_);
lean_dec_ref(v_lams_2011_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2024_, lean_object* v_lams_u2081_2025_, lean_object* v_as_2026_, size_t v_sz_2027_, size_t v_i_2028_, lean_object* v_b_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_a_2042_; uint8_t v___x_2046_; 
v___x_2046_ = lean_usize_dec_lt(v_i_2028_, v_sz_2027_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_b_2029_);
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; lean_object* v_a_2049_; 
v___x_2048_ = lean_box(0);
v_a_2049_ = lean_array_uget_borrowed(v_as_2026_, v_i_2028_);
if (lean_obj_tag(v_a_2049_) == 6)
{
lean_object* v_binderType_2050_; lean_object* v_body_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_binderType_2050_ = lean_ctor_get(v_a_2049_, 1);
v_body_2051_ = lean_ctor_get(v_a_2049_, 2);
v___x_2052_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_binderType_2050_);
v___x_2053_ = l_Lean_Meta_getLevel(v_binderType_2050_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2055_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2057_, 0, v_a_2054_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
lean_inc_ref(v___x_2057_);
v___x_2058_ = l_Lean_mkConst(v___x_2055_, v___x_2057_);
lean_inc_ref(v_binderType_2050_);
v___x_2059_ = l_Lean_Expr_app___override(v___x_2058_, v_binderType_2050_);
v___x_2060_ = lean_box(0);
v___x_2061_ = l_Lean_Meta_synthInstance_x3f(v___x_2059_, v___x_2060_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
if (lean_obj_tag(v_a_2062_) == 1)
{
lean_object* v_val_2063_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; uint8_t v___x_2128_; 
v_val_2063_ = lean_ctor_get(v_a_2062_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v_a_2062_, 1);
v___x_2128_ = l_Lean_Expr_hasLooseBVars(v_body_2051_);
if (v___x_2128_ == 0)
{
v___y_2065_ = v___y_2030_;
v___y_2066_ = v___y_2031_;
v___y_2067_ = v___y_2032_;
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
goto v___jp_2064_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2057_);
v___x_2130_ = l_Lean_mkConst(v___x_2129_, v___x_2057_);
lean_inc_ref(v_binderType_2050_);
v___x_2131_ = l_Lean_Expr_app___override(v___x_2130_, v_binderType_2050_);
v___x_2132_ = l_Lean_Meta_synthInstance_x3f(v___x_2131_, v___x_2060_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
if (lean_obj_tag(v_a_2133_) == 0)
{
lean_dec(v_val_2063_);
lean_dec_ref_known(v___x_2057_, 2);
v_a_2042_ = v___x_2048_;
goto v___jp_2041_;
}
else
{
lean_dec_ref_known(v_a_2133_, 1);
if (v___x_2128_ == 0)
{
lean_dec(v_val_2063_);
lean_dec_ref_known(v___x_2057_, 2);
v_a_2042_ = v___x_2048_;
goto v___jp_2041_;
}
else
{
v___y_2065_ = v___y_2030_;
v___y_2066_ = v___y_2031_;
v___y_2067_ = v___y_2032_;
v___y_2068_ = v___y_2033_;
v___y_2069_ = v___y_2034_;
v___y_2070_ = v___y_2035_;
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
goto v___jp_2064_;
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_val_2063_);
lean_dec_ref_known(v___x_2057_, 2);
v_a_2134_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2132_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2132_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
v___jp_2064_:
{
lean_object* v___x_2075_; 
v___x_2075_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2024_, v_binderType_2050_);
if (lean_obj_tag(v___x_2075_) == 1)
{
lean_object* v_val_2076_; 
v_val_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_val_2076_);
lean_dec_ref_known(v___x_2075_, 1);
if (lean_obj_tag(v_val_2076_) == 6)
{
lean_object* v_binderType_2077_; lean_object* v_body_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_binderType_2077_ = lean_ctor_get(v_val_2076_, 1);
lean_inc_ref(v_binderType_2077_);
v_body_2078_ = lean_ctor_get(v_val_2076_, 2);
lean_inc_ref(v_body_2078_);
lean_dec_ref_known(v_val_2076_, 3);
v___x_2079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2080_ = l_Lean_mkConst(v___x_2079_, v___x_2057_);
v___x_2081_ = l_Lean_mkAppB(v___x_2080_, v_binderType_2077_, v_val_2063_);
v___x_2082_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2081_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v___x_2084_ = lean_expr_instantiate1(v_body_2051_, v_a_2083_);
v___x_2085_ = lean_expr_instantiate1(v_body_2078_, v_a_2083_);
lean_dec_ref(v_body_2078_);
v___x_2086_ = lean_array_fget_borrowed(v_lams_u2081_2025_, v___x_2052_);
v___x_2087_ = lean_array_fget_borrowed(v_lams_u2082_2024_, v___x_2052_);
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
lean_inc(v___y_2068_);
lean_inc_ref(v___y_2067_);
lean_inc(v___y_2066_);
lean_inc(v___y_2065_);
lean_inc(v___x_2087_);
lean_inc(v___x_2086_);
v___x_2088_ = lean_grind_mk_eq_proof(v___x_2086_, v___x_2087_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2090_ = l_Lean_Meta_mkCongrFun(v_a_2089_, v_a_2083_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = l_Lean_Meta_mkEq(v___x_2084_, v___x_2085_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = l_Lean_Meta_mkExpectedPropHint(v_a_2091_, v_a_2093_);
v___x_2095_ = l_Lean_Meta_Grind_pushNewFact(v___x_2094_, v___x_2052_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref_known(v___x_2095_, 1);
v_a_2042_ = v___x_2048_;
goto v___jp_2041_;
}
else
{
return v___x_2095_;
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_a_2091_);
v_a_2096_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2092_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2092_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v___x_2085_);
lean_dec_ref(v___x_2084_);
v_a_2104_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2090_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2090_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v___x_2085_);
lean_dec_ref(v___x_2084_);
lean_dec(v_a_2083_);
v_a_2112_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2088_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2088_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_body_2078_);
v_a_2120_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2082_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2082_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_dec(v_val_2076_);
lean_dec(v_val_2063_);
lean_dec_ref_known(v___x_2057_, 2);
v_a_2042_ = v___x_2048_;
goto v___jp_2041_;
}
}
else
{
lean_dec(v___x_2075_);
lean_dec(v_val_2063_);
lean_dec_ref_known(v___x_2057_, 2);
v_a_2042_ = v___x_2048_;
goto v___jp_2041_;
}
}
}
else
{
lean_dec(v_a_2062_);
lean_dec_ref_known(v___x_2057_, 2);
v_a_2042_ = v___x_2048_;
goto v___jp_2041_;
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref_known(v___x_2057_, 2);
v_a_2142_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2061_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2061_);
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
v_a_2150_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2053_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2053_);
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
v_a_2042_ = v___x_2048_;
goto v___jp_2041_;
}
}
v___jp_2041_:
{
size_t v___x_2043_; size_t v___x_2044_; 
v___x_2043_ = ((size_t)1ULL);
v___x_2044_ = lean_usize_add(v_i_2028_, v___x_2043_);
v_i_2028_ = v___x_2044_;
v_b_2029_ = v_a_2042_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2158_ = _args[0];
lean_object* v_lams_u2081_2159_ = _args[1];
lean_object* v_as_2160_ = _args[2];
lean_object* v_sz_2161_ = _args[3];
lean_object* v_i_2162_ = _args[4];
lean_object* v_b_2163_ = _args[5];
lean_object* v___y_2164_ = _args[6];
lean_object* v___y_2165_ = _args[7];
lean_object* v___y_2166_ = _args[8];
lean_object* v___y_2167_ = _args[9];
lean_object* v___y_2168_ = _args[10];
lean_object* v___y_2169_ = _args[11];
lean_object* v___y_2170_ = _args[12];
lean_object* v___y_2171_ = _args[13];
lean_object* v___y_2172_ = _args[14];
lean_object* v___y_2173_ = _args[15];
lean_object* v___y_2174_ = _args[16];
_start:
{
size_t v_sz_boxed_2175_; size_t v_i_boxed_2176_; lean_object* v_res_2177_; 
v_sz_boxed_2175_ = lean_unbox_usize(v_sz_2161_);
lean_dec(v_sz_2161_);
v_i_boxed_2176_ = lean_unbox_usize(v_i_2162_);
lean_dec(v_i_2162_);
v_res_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2158_, v_lams_u2081_2159_, v_as_2160_, v_sz_boxed_2175_, v_i_boxed_2176_, v_b_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v_as_2160_);
lean_dec_ref(v_lams_u2081_2159_);
lean_dec_ref(v_lams_u2082_2158_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2178_, lean_object* v_lams_u2082_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2191_ = lean_array_get_size(v_lams_u2081_2178_);
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = lean_nat_dec_eq(v___x_2191_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2194_ = lean_array_get_size(v_lams_u2082_2179_);
v___x_2195_ = lean_nat_dec_eq(v___x_2194_, v___x_2192_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; size_t v_sz_2197_; size_t v___x_2198_; lean_object* v___x_2199_; 
v___x_2196_ = lean_box(0);
v_sz_2197_ = lean_array_size(v_lams_u2081_2178_);
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2179_, v_lams_u2081_2178_, v_lams_u2081_2178_, v_sz_2197_, v___x_2198_, v___x_2196_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v___x_2199_, 0);
lean_dec(v_unused_2207_);
v___x_2201_ = v___x_2199_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_dec(v___x_2199_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2196_);
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2196_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
else
{
return v___x_2199_;
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2212_, lean_object* v_lams_u2082_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2212_, v_lams_u2082_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_lams_u2082_2213_);
lean_dec_ref(v_lams_u2081_2212_);
return v_res_2225_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2226_){
_start:
{
uint8_t v___x_2227_; 
v___x_2227_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2228_){
_start:
{
uint8_t v_res_2229_; lean_object* v_r_2230_; 
v_res_2229_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2228_);
lean_dec_ref(v_x_2228_);
v_r_2230_ = lean_box(v_res_2229_);
return v_r_2230_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2231_, lean_object* v_x_2232_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2234_, lean_object* v_x_2235_){
_start:
{
uint8_t v_res_2236_; lean_object* v_r_2237_; 
v_res_2236_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2234_, v_x_2235_);
lean_dec_ref(v_x_2235_);
v_r_2237_ = lean_box(v_res_2236_);
return v_r_2237_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2238_, lean_object* v_v_2239_, lean_object* v_i_2240_){
_start:
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = lean_array_get_size(v_xs_2238_);
v___x_2242_ = lean_nat_dec_lt(v_i_2240_, v___x_2241_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
lean_dec(v_i_2240_);
v___x_2243_ = lean_box(0);
return v___x_2243_;
}
else
{
lean_object* v___x_2244_; size_t v___x_2245_; size_t v___x_2246_; uint8_t v___x_2247_; 
v___x_2244_ = lean_array_fget_borrowed(v_xs_2238_, v_i_2240_);
v___x_2245_ = lean_ptr_addr(v___x_2244_);
v___x_2246_ = lean_ptr_addr(v_v_2239_);
v___x_2247_ = lean_usize_dec_eq(v___x_2245_, v___x_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_nat_add(v_i_2240_, v___x_2248_);
lean_dec(v_i_2240_);
v_i_2240_ = v___x_2249_;
goto _start;
}
else
{
lean_object* v___x_2251_; 
v___x_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_i_2240_);
return v___x_2251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2252_, lean_object* v_v_2253_, lean_object* v_i_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2252_, v_v_2253_, v_i_2254_);
lean_dec_ref(v_v_2253_);
lean_dec_ref(v_xs_2252_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2256_, lean_object* v_v_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2256_, v_v_2257_, v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2260_, lean_object* v_v_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2260_, v_v_2261_);
lean_dec_ref(v_v_2261_);
lean_dec_ref(v_xs_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2263_, size_t v_x_2264_, lean_object* v_x_2265_){
_start:
{
if (lean_obj_tag(v_x_2263_) == 0)
{
lean_object* v_es_2266_; lean_object* v___x_2267_; size_t v___x_2268_; size_t v___x_2269_; lean_object* v_j_2270_; lean_object* v_entry_2271_; 
v_es_2266_ = lean_ctor_get(v_x_2263_, 0);
v___x_2267_ = lean_box(2);
v___x_2268_ = ((size_t)31ULL);
v___x_2269_ = lean_usize_land(v_x_2264_, v___x_2268_);
v_j_2270_ = lean_usize_to_nat(v___x_2269_);
v_entry_2271_ = lean_array_get(v___x_2267_, v_es_2266_, v_j_2270_);
switch(lean_obj_tag(v_entry_2271_))
{
case 0:
{
lean_object* v_key_2272_; size_t v___x_2273_; size_t v___x_2274_; uint8_t v___x_2275_; 
v_key_2272_ = lean_ctor_get(v_entry_2271_, 0);
lean_inc(v_key_2272_);
lean_dec_ref_known(v_entry_2271_, 2);
v___x_2273_ = lean_ptr_addr(v_x_2265_);
v___x_2274_ = lean_ptr_addr(v_key_2272_);
lean_dec(v_key_2272_);
v___x_2275_ = lean_usize_dec_eq(v___x_2273_, v___x_2274_);
if (v___x_2275_ == 0)
{
lean_dec(v_j_2270_);
return v_x_2263_;
}
else
{
lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2283_; 
lean_inc_ref(v_es_2266_);
v_isSharedCheck_2283_ = !lean_is_exclusive(v_x_2263_);
if (v_isSharedCheck_2283_ == 0)
{
lean_object* v_unused_2284_; 
v_unused_2284_ = lean_ctor_get(v_x_2263_, 0);
lean_dec(v_unused_2284_);
v___x_2277_ = v_x_2263_;
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
else
{
lean_dec(v_x_2263_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2283_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2279_ = lean_array_set(v_es_2266_, v_j_2270_, v___x_2267_);
lean_dec(v_j_2270_);
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
lean_inc_ref(v_es_2266_);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_x_2263_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_x_2263_, 0);
lean_dec(v_unused_2320_);
v___x_2286_ = v_x_2263_;
v_isShared_2287_ = v_isSharedCheck_2319_;
goto v_resetjp_2285_;
}
else
{
lean_dec(v_x_2263_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2319_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_node_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2318_; 
v_node_2288_ = lean_ctor_get(v_entry_2271_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_entry_2271_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2290_ = v_entry_2271_;
v_isShared_2291_ = v_isSharedCheck_2318_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_node_2288_);
lean_dec(v_entry_2271_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2318_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
size_t v___x_2292_; lean_object* v_entries_2293_; size_t v___x_2294_; lean_object* v_newNode_2295_; lean_object* v___x_2296_; 
v___x_2292_ = ((size_t)5ULL);
v_entries_2293_ = lean_array_set(v_es_2266_, v_j_2270_, v___x_2267_);
v___x_2294_ = lean_usize_shift_right(v_x_2264_, v___x_2292_);
v_newNode_2295_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2288_, v___x_2294_, v_x_2265_);
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
v___x_2299_ = lean_array_set(v_entries_2293_, v_j_2270_, v___x_2298_);
lean_dec(v_j_2270_);
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
v___x_2312_ = lean_array_set(v_entries_2293_, v_j_2270_, v___x_2311_);
lean_dec(v_j_2270_);
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
lean_dec(v_j_2270_);
return v_x_2263_;
}
}
}
else
{
lean_object* v_ks_2321_; lean_object* v_vs_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2336_; 
v_ks_2321_ = lean_ctor_get(v_x_2263_, 0);
v_vs_2322_ = lean_ctor_get(v_x_2263_, 1);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_x_2263_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2324_ = v_x_2263_;
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_vs_2322_);
lean_inc(v_ks_2321_);
lean_dec(v_x_2263_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2336_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2321_, v_x_2265_);
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
size_t v_x_19389__boxed_2340_; lean_object* v_res_2341_; 
v_x_19389__boxed_2340_ = lean_unbox_usize(v_x_2338_);
lean_dec(v_x_2338_);
v_res_2341_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2337_, v_x_19389__boxed_2340_, v_x_2339_);
lean_dec_ref(v_x_2339_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
size_t v___x_2344_; size_t v___x_2345_; size_t v___x_2346_; uint64_t v___x_2347_; size_t v_h_2348_; lean_object* v___x_2349_; 
v___x_2344_ = lean_ptr_addr(v_x_2343_);
v___x_2345_ = ((size_t)3ULL);
v___x_2346_ = lean_usize_shift_right(v___x_2344_, v___x_2345_);
v___x_2347_ = lean_usize_to_uint64(v___x_2346_);
v_h_2348_ = lean_uint64_to_usize(v___x_2347_);
v___x_2349_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2342_, v_h_2348_, v_x_2343_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2350_, lean_object* v_x_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2350_, v_x_2351_);
lean_dec_ref(v_x_2351_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
if (lean_obj_tag(v_as_2353_) == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_box(0);
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
else
{
lean_object* v_head_2367_; lean_object* v_tail_2368_; lean_object* v___x_2369_; 
v_head_2367_ = lean_ctor_get(v_as_2353_, 0);
lean_inc(v_head_2367_);
v_tail_2368_ = lean_ctor_get(v_as_2353_, 1);
lean_inc(v_tail_2368_);
lean_dec_ref_known(v_as_2353_, 2);
v___x_2369_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2367_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_dec_ref_known(v___x_2369_, 1);
v_as_2353_ = v_tail_2368_;
goto _start;
}
else
{
lean_dec(v_tail_2368_);
return v___x_2369_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec(v___y_2372_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2384_, lean_object* v_vals_2385_, lean_object* v_i_2386_, lean_object* v_k_2387_){
_start:
{
lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = lean_array_get_size(v_keys_2384_);
v___x_2389_ = lean_nat_dec_lt(v_i_2386_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; 
lean_dec(v_i_2386_);
v___x_2390_ = lean_box(0);
return v___x_2390_;
}
else
{
lean_object* v_k_x27_2391_; size_t v___x_2392_; size_t v___x_2393_; uint8_t v___x_2394_; 
v_k_x27_2391_ = lean_array_fget_borrowed(v_keys_2384_, v_i_2386_);
v___x_2392_ = lean_ptr_addr(v_k_2387_);
v___x_2393_ = lean_ptr_addr(v_k_x27_2391_);
v___x_2394_ = lean_usize_dec_eq(v___x_2392_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_unsigned_to_nat(1u);
v___x_2396_ = lean_nat_add(v_i_2386_, v___x_2395_);
lean_dec(v_i_2386_);
v_i_2386_ = v___x_2396_;
goto _start;
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_array_fget_borrowed(v_vals_2385_, v_i_2386_);
lean_dec(v_i_2386_);
lean_inc(v___x_2398_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2400_, lean_object* v_vals_2401_, lean_object* v_i_2402_, lean_object* v_k_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2400_, v_vals_2401_, v_i_2402_, v_k_2403_);
lean_dec_ref(v_k_2403_);
lean_dec_ref(v_vals_2401_);
lean_dec_ref(v_keys_2400_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2405_, size_t v_x_2406_, lean_object* v_x_2407_){
_start:
{
if (lean_obj_tag(v_x_2405_) == 0)
{
lean_object* v_es_2408_; lean_object* v___x_2409_; size_t v___x_2410_; size_t v___x_2411_; lean_object* v_j_2412_; lean_object* v___x_2413_; 
v_es_2408_ = lean_ctor_get(v_x_2405_, 0);
v___x_2409_ = lean_box(2);
v___x_2410_ = ((size_t)31ULL);
v___x_2411_ = lean_usize_land(v_x_2406_, v___x_2410_);
v_j_2412_ = lean_usize_to_nat(v___x_2411_);
v___x_2413_ = lean_array_get_borrowed(v___x_2409_, v_es_2408_, v_j_2412_);
lean_dec(v_j_2412_);
switch(lean_obj_tag(v___x_2413_))
{
case 0:
{
lean_object* v_key_2414_; lean_object* v_val_2415_; size_t v___x_2416_; size_t v___x_2417_; uint8_t v___x_2418_; 
v_key_2414_ = lean_ctor_get(v___x_2413_, 0);
v_val_2415_ = lean_ctor_get(v___x_2413_, 1);
v___x_2416_ = lean_ptr_addr(v_x_2407_);
v___x_2417_ = lean_ptr_addr(v_key_2414_);
v___x_2418_ = lean_usize_dec_eq(v___x_2416_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_box(0);
return v___x_2419_;
}
else
{
lean_object* v___x_2420_; 
lean_inc(v_val_2415_);
v___x_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_val_2415_);
return v___x_2420_;
}
}
case 1:
{
lean_object* v_node_2421_; size_t v___x_2422_; size_t v___x_2423_; 
v_node_2421_ = lean_ctor_get(v___x_2413_, 0);
v___x_2422_ = ((size_t)5ULL);
v___x_2423_ = lean_usize_shift_right(v_x_2406_, v___x_2422_);
v_x_2405_ = v_node_2421_;
v_x_2406_ = v___x_2423_;
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
v_ks_2426_ = lean_ctor_get(v_x_2405_, 0);
v_vs_2427_ = lean_ctor_get(v_x_2405_, 1);
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2426_, v_vs_2427_, v___x_2428_, v_x_2407_);
return v___x_2429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
size_t v_x_19614__boxed_2433_; lean_object* v_res_2434_; 
v_x_19614__boxed_2433_ = lean_unbox_usize(v_x_2431_);
lean_dec(v_x_2431_);
v_res_2434_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2430_, v_x_19614__boxed_2433_, v_x_2432_);
lean_dec_ref(v_x_2432_);
lean_dec_ref(v_x_2430_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
size_t v___x_2437_; size_t v___x_2438_; size_t v___x_2439_; uint64_t v___x_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
v___x_2437_ = lean_ptr_addr(v_x_2436_);
v___x_2438_ = ((size_t)3ULL);
v___x_2439_ = lean_usize_shift_right(v___x_2437_, v___x_2438_);
v___x_2440_ = lean_usize_to_uint64(v___x_2439_);
v___x_2441_ = lean_uint64_to_usize(v___x_2440_);
v___x_2442_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2435_, v___x_2441_, v_x_2436_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2443_, v_x_2444_);
lean_dec_ref(v_x_2444_);
lean_dec_ref(v_x_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2446_, lean_object* v_b_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
if (lean_obj_tag(v_as_x27_2446_) == 0)
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2459_, 0, v_b_2447_);
return v___x_2459_;
}
else
{
lean_object* v_head_2460_; lean_object* v_tail_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v_toGoalState_2464_; lean_object* v_ematch_2465_; lean_object* v_delayedThmInsts_2466_; lean_object* v___x_2467_; 
v_head_2460_ = lean_ctor_get(v_as_x27_2446_, 0);
v_tail_2461_ = lean_ctor_get(v_as_x27_2446_, 1);
v___x_2462_ = lean_box(0);
v___x_2463_ = lean_st_ref_get(v___y_2448_);
v_toGoalState_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc_ref(v_toGoalState_2464_);
lean_dec(v___x_2463_);
v_ematch_2465_ = lean_ctor_get(v_toGoalState_2464_, 12);
lean_inc_ref(v_ematch_2465_);
lean_dec_ref(v_toGoalState_2464_);
v_delayedThmInsts_2466_ = lean_ctor_get(v_ematch_2465_, 10);
lean_inc_ref(v_delayedThmInsts_2466_);
lean_dec_ref(v_ematch_2465_);
v___x_2467_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2466_, v_head_2460_);
lean_dec_ref(v_delayedThmInsts_2466_);
if (lean_obj_tag(v___x_2467_) == 1)
{
lean_object* v_val_2468_; lean_object* v___x_2469_; lean_object* v_toGoalState_2470_; lean_object* v_ematch_2471_; lean_object* v_mvarId_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2526_; 
v_val_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2469_ = lean_st_ref_take(v___y_2448_);
v_toGoalState_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc_ref(v_toGoalState_2470_);
v_ematch_2471_ = lean_ctor_get(v_toGoalState_2470_, 12);
lean_inc_ref(v_ematch_2471_);
v_mvarId_2472_ = lean_ctor_get(v___x_2469_, 1);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v___x_2469_, 0);
lean_dec(v_unused_2527_);
v___x_2474_ = v___x_2469_;
v_isShared_2475_ = v_isSharedCheck_2526_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_mvarId_2472_);
lean_dec(v___x_2469_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2526_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_nextDeclIdx_2476_; lean_object* v_enodeMap_2477_; lean_object* v_exprs_2478_; lean_object* v_parents_2479_; lean_object* v_congrTable_2480_; lean_object* v_appMap_2481_; lean_object* v_indicesFound_2482_; lean_object* v_newFacts_2483_; uint8_t v_inconsistent_2484_; lean_object* v_nextIdx_2485_; lean_object* v_newRawFacts_2486_; lean_object* v_facts_2487_; lean_object* v_extThms_2488_; lean_object* v_inj_2489_; lean_object* v_split_2490_; lean_object* v_clean_2491_; lean_object* v_sstates_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2524_; 
v_nextDeclIdx_2476_ = lean_ctor_get(v_toGoalState_2470_, 0);
v_enodeMap_2477_ = lean_ctor_get(v_toGoalState_2470_, 1);
v_exprs_2478_ = lean_ctor_get(v_toGoalState_2470_, 2);
v_parents_2479_ = lean_ctor_get(v_toGoalState_2470_, 3);
v_congrTable_2480_ = lean_ctor_get(v_toGoalState_2470_, 4);
v_appMap_2481_ = lean_ctor_get(v_toGoalState_2470_, 5);
v_indicesFound_2482_ = lean_ctor_get(v_toGoalState_2470_, 6);
v_newFacts_2483_ = lean_ctor_get(v_toGoalState_2470_, 7);
v_inconsistent_2484_ = lean_ctor_get_uint8(v_toGoalState_2470_, sizeof(void*)*17);
v_nextIdx_2485_ = lean_ctor_get(v_toGoalState_2470_, 8);
v_newRawFacts_2486_ = lean_ctor_get(v_toGoalState_2470_, 9);
v_facts_2487_ = lean_ctor_get(v_toGoalState_2470_, 10);
v_extThms_2488_ = lean_ctor_get(v_toGoalState_2470_, 11);
v_inj_2489_ = lean_ctor_get(v_toGoalState_2470_, 13);
v_split_2490_ = lean_ctor_get(v_toGoalState_2470_, 14);
v_clean_2491_ = lean_ctor_get(v_toGoalState_2470_, 15);
v_sstates_2492_ = lean_ctor_get(v_toGoalState_2470_, 16);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_toGoalState_2470_);
if (v_isSharedCheck_2524_ == 0)
{
lean_object* v_unused_2525_; 
v_unused_2525_ = lean_ctor_get(v_toGoalState_2470_, 12);
lean_dec(v_unused_2525_);
v___x_2494_ = v_toGoalState_2470_;
v_isShared_2495_ = v_isSharedCheck_2524_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_sstates_2492_);
lean_inc(v_clean_2491_);
lean_inc(v_split_2490_);
lean_inc(v_inj_2489_);
lean_inc(v_extThms_2488_);
lean_inc(v_facts_2487_);
lean_inc(v_newRawFacts_2486_);
lean_inc(v_nextIdx_2485_);
lean_inc(v_newFacts_2483_);
lean_inc(v_indicesFound_2482_);
lean_inc(v_appMap_2481_);
lean_inc(v_congrTable_2480_);
lean_inc(v_parents_2479_);
lean_inc(v_exprs_2478_);
lean_inc(v_enodeMap_2477_);
lean_inc(v_nextDeclIdx_2476_);
lean_dec(v_toGoalState_2470_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2524_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_thmMap_2496_; lean_object* v_gmt_2497_; lean_object* v_thms_2498_; lean_object* v_newThms_2499_; lean_object* v_numInstances_2500_; lean_object* v_numDelayedInstances_2501_; lean_object* v_num_2502_; lean_object* v_preInstances_2503_; lean_object* v_nextThmIdx_2504_; lean_object* v_matchEqNames_2505_; lean_object* v_delayedThmInsts_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2523_; 
v_thmMap_2496_ = lean_ctor_get(v_ematch_2471_, 0);
v_gmt_2497_ = lean_ctor_get(v_ematch_2471_, 1);
v_thms_2498_ = lean_ctor_get(v_ematch_2471_, 2);
v_newThms_2499_ = lean_ctor_get(v_ematch_2471_, 3);
v_numInstances_2500_ = lean_ctor_get(v_ematch_2471_, 4);
v_numDelayedInstances_2501_ = lean_ctor_get(v_ematch_2471_, 5);
v_num_2502_ = lean_ctor_get(v_ematch_2471_, 6);
v_preInstances_2503_ = lean_ctor_get(v_ematch_2471_, 7);
v_nextThmIdx_2504_ = lean_ctor_get(v_ematch_2471_, 8);
v_matchEqNames_2505_ = lean_ctor_get(v_ematch_2471_, 9);
v_delayedThmInsts_2506_ = lean_ctor_get(v_ematch_2471_, 10);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_ematch_2471_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2508_ = v_ematch_2471_;
v_isShared_2509_ = v_isSharedCheck_2523_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_delayedThmInsts_2506_);
lean_inc(v_matchEqNames_2505_);
lean_inc(v_nextThmIdx_2504_);
lean_inc(v_preInstances_2503_);
lean_inc(v_num_2502_);
lean_inc(v_numDelayedInstances_2501_);
lean_inc(v_numInstances_2500_);
lean_inc(v_newThms_2499_);
lean_inc(v_thms_2498_);
lean_inc(v_gmt_2497_);
lean_inc(v_thmMap_2496_);
lean_dec(v_ematch_2471_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2523_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2510_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2506_, v_head_2460_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 10, v___x_2510_);
v___x_2512_ = v___x_2508_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_thmMap_2496_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_gmt_2497_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_thms_2498_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_newThms_2499_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_numInstances_2500_);
lean_ctor_set(v_reuseFailAlloc_2522_, 5, v_numDelayedInstances_2501_);
lean_ctor_set(v_reuseFailAlloc_2522_, 6, v_num_2502_);
lean_ctor_set(v_reuseFailAlloc_2522_, 7, v_preInstances_2503_);
lean_ctor_set(v_reuseFailAlloc_2522_, 8, v_nextThmIdx_2504_);
lean_ctor_set(v_reuseFailAlloc_2522_, 9, v_matchEqNames_2505_);
lean_ctor_set(v_reuseFailAlloc_2522_, 10, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2514_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 12, v___x_2512_);
v___x_2514_ = v___x_2494_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_nextDeclIdx_2476_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_enodeMap_2477_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_exprs_2478_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v_parents_2479_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v_congrTable_2480_);
lean_ctor_set(v_reuseFailAlloc_2521_, 5, v_appMap_2481_);
lean_ctor_set(v_reuseFailAlloc_2521_, 6, v_indicesFound_2482_);
lean_ctor_set(v_reuseFailAlloc_2521_, 7, v_newFacts_2483_);
lean_ctor_set(v_reuseFailAlloc_2521_, 8, v_nextIdx_2485_);
lean_ctor_set(v_reuseFailAlloc_2521_, 9, v_newRawFacts_2486_);
lean_ctor_set(v_reuseFailAlloc_2521_, 10, v_facts_2487_);
lean_ctor_set(v_reuseFailAlloc_2521_, 11, v_extThms_2488_);
lean_ctor_set(v_reuseFailAlloc_2521_, 12, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2521_, 13, v_inj_2489_);
lean_ctor_set(v_reuseFailAlloc_2521_, 14, v_split_2490_);
lean_ctor_set(v_reuseFailAlloc_2521_, 15, v_clean_2491_);
lean_ctor_set(v_reuseFailAlloc_2521_, 16, v_sstates_2492_);
lean_ctor_set_uint8(v_reuseFailAlloc_2521_, sizeof(void*)*17, v_inconsistent_2484_);
v___x_2514_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2514_);
v___x_2516_ = v___x_2474_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_mvarId_2472_);
v___x_2516_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_st_ref_put(v___y_2448_, v___x_2516_);
v___x_2518_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2468_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_dec_ref_known(v___x_2518_, 1);
v_as_x27_2446_ = v_tail_2461_;
v_b_2447_ = v___x_2462_;
goto _start;
}
else
{
return v___x_2518_;
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
lean_dec(v___x_2467_);
v_as_x27_2446_ = v_tail_2461_;
v_b_2447_ = v___x_2462_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2529_, lean_object* v_b_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2529_, v_b_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec(v_as_x27_2529_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2544_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2584_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2584_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2584_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
uint8_t v___x_2560_; 
v___x_2560_ = lean_unbox(v_a_2556_);
lean_dec(v_a_2556_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v_toGoalState_2562_; lean_object* v_ematch_2563_; lean_object* v_delayedThmInsts_2564_; uint8_t v___x_2565_; 
v___x_2561_ = lean_st_ref_get(v_a_2544_);
v_toGoalState_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc_ref(v_toGoalState_2562_);
lean_dec(v___x_2561_);
v_ematch_2563_ = lean_ctor_get(v_toGoalState_2562_, 12);
lean_inc_ref(v_ematch_2563_);
lean_dec_ref(v_toGoalState_2562_);
v_delayedThmInsts_2564_ = lean_ctor_get(v_ematch_2563_, 10);
lean_inc_ref(v_delayedThmInsts_2564_);
lean_dec_ref(v_ematch_2563_);
v___x_2565_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2564_);
lean_dec_ref(v_delayedThmInsts_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_del_object(v___x_2558_);
v___x_2566_ = lean_box(0);
v___x_2567_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2543_, v___x_2566_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2574_ == 0)
{
lean_object* v_unused_2575_; 
v_unused_2575_ = lean_ctor_get(v___x_2567_, 0);
lean_dec(v_unused_2575_);
v___x_2569_ = v___x_2567_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_dec(v___x_2567_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2566_);
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2566_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
else
{
return v___x_2567_;
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2576_ = lean_box(0);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2576_);
v___x_2578_ = v___x_2558_;
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
else
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
v___x_2580_ = lean_box(0);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2580_);
v___x_2582_ = v___x_2558_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v_a_2585_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2555_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2555_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec(v_a_2594_);
lean_dec(v_toPropagateDown_2593_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2607_, v_x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2610_, lean_object* v_x_2611_, lean_object* v_x_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2610_, v_x_2611_, v_x_2612_);
lean_dec_ref(v_x_2612_);
lean_dec_ref(v_x_2611_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2614_, lean_object* v_x_2615_, lean_object* v_x_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2615_, v_x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2618_, v_x_2619_, v_x_2620_);
lean_dec_ref(v_x_2620_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2622_, lean_object* v_as_x27_2623_, lean_object* v_b_2624_, lean_object* v_a_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2623_, v_b_2624_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2638_, lean_object* v_as_x27_2639_, lean_object* v_b_2640_, lean_object* v_a_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2638_, v_as_x27_2639_, v_b_2640_, v_a_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec(v_as_x27_2639_);
lean_dec(v_as_2638_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2654_, lean_object* v_x_2655_, size_t v_x_2656_, lean_object* v_x_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2655_, v_x_2656_, v_x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2659_, lean_object* v_x_2660_, lean_object* v_x_2661_, lean_object* v_x_2662_){
_start:
{
size_t v_x_19919__boxed_2663_; lean_object* v_res_2664_; 
v_x_19919__boxed_2663_ = lean_unbox_usize(v_x_2661_);
lean_dec(v_x_2661_);
v_res_2664_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2659_, v_x_2660_, v_x_19919__boxed_2663_, v_x_2662_);
lean_dec_ref(v_x_2662_);
lean_dec_ref(v_x_2660_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2665_, lean_object* v_x_2666_, size_t v_x_2667_, lean_object* v_x_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2666_, v_x_2667_, v_x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2670_, lean_object* v_x_2671_, lean_object* v_x_2672_, lean_object* v_x_2673_){
_start:
{
size_t v_x_19930__boxed_2674_; lean_object* v_res_2675_; 
v_x_19930__boxed_2674_ = lean_unbox_usize(v_x_2672_);
lean_dec(v_x_2672_);
v_res_2675_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2670_, v_x_2671_, v_x_19930__boxed_2674_, v_x_2673_);
lean_dec_ref(v_x_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2676_, lean_object* v_keys_2677_, lean_object* v_vals_2678_, lean_object* v_heq_2679_, lean_object* v_i_2680_, lean_object* v_k_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2677_, v_vals_2678_, v_i_2680_, v_k_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2683_, lean_object* v_keys_2684_, lean_object* v_vals_2685_, lean_object* v_heq_2686_, lean_object* v_i_2687_, lean_object* v_k_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2683_, v_keys_2684_, v_vals_2685_, v_heq_2686_, v_i_2687_, v_k_2688_);
lean_dec_ref(v_k_2688_);
lean_dec_ref(v_vals_2685_);
lean_dec_ref(v_keys_2684_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2690_, lean_object* v_keys_2691_, lean_object* v_vals_2692_, lean_object* v_i_2693_, lean_object* v_k_2694_){
_start:
{
lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = lean_array_get_size(v_keys_2691_);
v___x_2696_ = lean_nat_dec_lt(v_i_2693_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; 
lean_dec_ref(v_k_2694_);
lean_dec(v_i_2693_);
v___x_2697_ = lean_box(0);
return v___x_2697_;
}
else
{
lean_object* v_k_x27_2698_; uint8_t v___x_2699_; 
v_k_x27_2698_ = lean_array_fget_borrowed(v_keys_2691_, v_i_2693_);
lean_inc(v_k_x27_2698_);
lean_inc_ref(v_k_2694_);
v___x_2699_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2690_, v_k_2694_, v_k_x27_2698_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_unsigned_to_nat(1u);
v___x_2701_ = lean_nat_add(v_i_2693_, v___x_2700_);
lean_dec(v_i_2693_);
v_i_2693_ = v___x_2701_;
goto _start;
}
else
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_dec_ref(v_k_2694_);
v___x_2703_ = lean_array_fget_borrowed(v_vals_2692_, v_i_2693_);
lean_dec(v_i_2693_);
lean_inc(v___x_2703_);
lean_inc(v_k_x27_2698_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_k_x27_2698_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2706_, lean_object* v_keys_2707_, lean_object* v_vals_2708_, lean_object* v_i_2709_, lean_object* v_k_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2706_, v_keys_2707_, v_vals_2708_, v_i_2709_, v_k_2710_);
lean_dec_ref(v_vals_2708_);
lean_dec_ref(v_keys_2707_);
lean_dec_ref(v___x_2706_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2712_, lean_object* v_x_2713_, size_t v_x_2714_, lean_object* v_x_2715_){
_start:
{
if (lean_obj_tag(v_x_2713_) == 0)
{
lean_object* v_es_2716_; lean_object* v___x_2717_; size_t v___x_2718_; size_t v___x_2719_; lean_object* v_j_2720_; lean_object* v___x_2721_; 
v_es_2716_ = lean_ctor_get(v_x_2713_, 0);
lean_inc_ref(v_es_2716_);
lean_dec_ref_known(v_x_2713_, 1);
v___x_2717_ = lean_box(2);
v___x_2718_ = ((size_t)31ULL);
v___x_2719_ = lean_usize_land(v_x_2714_, v___x_2718_);
v_j_2720_ = lean_usize_to_nat(v___x_2719_);
v___x_2721_ = lean_array_get(v___x_2717_, v_es_2716_, v_j_2720_);
lean_dec(v_j_2720_);
lean_dec_ref(v_es_2716_);
switch(lean_obj_tag(v___x_2721_))
{
case 0:
{
lean_object* v_key_2722_; lean_object* v_val_2723_; uint8_t v___x_2724_; 
v_key_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc_n(v_key_2722_, 2);
v_val_2723_ = lean_ctor_get(v___x_2721_, 1);
lean_inc(v_val_2723_);
lean_dec_ref_known(v___x_2721_, 2);
v___x_2724_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2712_, v_x_2715_, v_key_2722_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
lean_dec(v_val_2723_);
lean_dec(v_key_2722_);
v___x_2725_ = lean_box(0);
return v___x_2725_;
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v_key_2722_);
lean_ctor_set(v___x_2726_, 1, v_val_2723_);
v___x_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
return v___x_2727_;
}
}
case 1:
{
lean_object* v_node_2728_; size_t v___x_2729_; size_t v___x_2730_; 
v_node_2728_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_node_2728_);
lean_dec_ref_known(v___x_2721_, 1);
v___x_2729_ = ((size_t)5ULL);
v___x_2730_ = lean_usize_shift_right(v_x_2714_, v___x_2729_);
v_x_2713_ = v_node_2728_;
v_x_2714_ = v___x_2730_;
goto _start;
}
default: 
{
lean_object* v___x_2732_; 
lean_dec_ref(v_x_2715_);
v___x_2732_ = lean_box(0);
return v___x_2732_;
}
}
}
else
{
lean_object* v_ks_2733_; lean_object* v_vs_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_ks_2733_ = lean_ctor_get(v_x_2713_, 0);
lean_inc_ref(v_ks_2733_);
v_vs_2734_ = lean_ctor_get(v_x_2713_, 1);
lean_inc_ref(v_vs_2734_);
lean_dec_ref_known(v_x_2713_, 2);
v___x_2735_ = lean_unsigned_to_nat(0u);
v___x_2736_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2712_, v_ks_2733_, v_vs_2734_, v___x_2735_, v_x_2715_);
lean_dec_ref(v_vs_2734_);
lean_dec_ref(v_ks_2733_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2737_, lean_object* v_x_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_){
_start:
{
size_t v_x_25951__boxed_2741_; lean_object* v_res_2742_; 
v_x_25951__boxed_2741_ = lean_unbox_usize(v_x_2739_);
lean_dec(v_x_2739_);
v_res_2742_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2737_, v_x_2738_, v_x_25951__boxed_2741_, v_x_2740_);
lean_dec_ref(v___x_2737_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2743_, lean_object* v_x_2744_, lean_object* v_x_2745_){
_start:
{
uint64_t v___x_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
lean_inc_ref(v_x_2745_);
v___x_2746_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2743_, v_x_2745_);
v___x_2747_ = lean_uint64_to_usize(v___x_2746_);
lean_inc_ref(v_x_2744_);
v___x_2748_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2743_, v_x_2744_, v___x_2747_, v_x_2745_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2749_, v_x_2750_, v_x_2751_);
lean_dec_ref(v_x_2750_);
lean_dec_ref(v___x_2749_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_){
_start:
{
lean_object* v_ks_2758_; lean_object* v_vs_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2783_; 
v_ks_2758_ = lean_ctor_get(v_x_2754_, 0);
v_vs_2759_ = lean_ctor_get(v_x_2754_, 1);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_x_2754_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2761_ = v_x_2754_;
v_isShared_2762_ = v_isSharedCheck_2783_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_vs_2759_);
lean_inc(v_ks_2758_);
lean_dec(v_x_2754_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2783_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = lean_array_get_size(v_ks_2758_);
v___x_2764_ = lean_nat_dec_lt(v_x_2755_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_dec(v_x_2755_);
v___x_2765_ = lean_array_push(v_ks_2758_, v_x_2756_);
v___x_2766_ = lean_array_push(v_vs_2759_, v_x_2757_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2766_);
lean_ctor_set(v___x_2761_, 0, v___x_2765_);
v___x_2768_ = v___x_2761_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
else
{
lean_object* v_k_x27_2770_; uint8_t v___x_2771_; 
v_k_x27_2770_ = lean_array_fget_borrowed(v_ks_2758_, v_x_2755_);
lean_inc(v_k_x27_2770_);
lean_inc_ref(v_x_2756_);
v___x_2771_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2753_, v_x_2756_, v_k_x27_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2773_; 
if (v_isShared_2762_ == 0)
{
v___x_2773_ = v___x_2761_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_ks_2758_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_vs_2759_);
v___x_2773_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_unsigned_to_nat(1u);
v___x_2775_ = lean_nat_add(v_x_2755_, v___x_2774_);
lean_dec(v_x_2755_);
v_x_2754_ = v___x_2773_;
v_x_2755_ = v___x_2775_;
goto _start;
}
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2778_ = lean_array_fset(v_ks_2758_, v_x_2755_, v_x_2756_);
v___x_2779_ = lean_array_fset(v_vs_2759_, v_x_2755_, v_x_2757_);
lean_dec(v_x_2755_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 1, v___x_2779_);
lean_ctor_set(v___x_2761_, 0, v___x_2778_);
v___x_2781_ = v___x_2761_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2784_, lean_object* v_x_2785_, lean_object* v_x_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2784_, v_x_2785_, v_x_2786_, v_x_2787_, v_x_2788_);
lean_dec_ref(v___x_2784_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2790_, lean_object* v_n_2791_, lean_object* v_k_2792_, lean_object* v_v_2793_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_unsigned_to_nat(0u);
v___x_2795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2790_, v_n_2791_, v___x_2794_, v_k_2792_, v_v_2793_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2796_, lean_object* v_n_2797_, lean_object* v_k_2798_, lean_object* v_v_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2796_, v_n_2797_, v_k_2798_, v_v_2799_);
lean_dec_ref(v___x_2796_);
return v_res_2800_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2802_, lean_object* v_x_2803_, size_t v_x_2804_, size_t v_x_2805_, lean_object* v_x_2806_, lean_object* v_x_2807_){
_start:
{
if (lean_obj_tag(v_x_2803_) == 0)
{
lean_object* v_es_2808_; size_t v___x_2809_; size_t v___x_2810_; lean_object* v_j_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v_es_2808_ = lean_ctor_get(v_x_2803_, 0);
v___x_2809_ = ((size_t)31ULL);
v___x_2810_ = lean_usize_land(v_x_2804_, v___x_2809_);
v_j_2811_ = lean_usize_to_nat(v___x_2810_);
v___x_2812_ = lean_array_get_size(v_es_2808_);
v___x_2813_ = lean_nat_dec_lt(v_j_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_dec(v_j_2811_);
lean_dec(v_x_2807_);
lean_dec_ref(v_x_2806_);
return v_x_2803_;
}
else
{
lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2852_; 
lean_inc_ref(v_es_2808_);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_x_2803_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; 
v_unused_2853_ = lean_ctor_get(v_x_2803_, 0);
lean_dec(v_unused_2853_);
v___x_2815_ = v_x_2803_;
v_isShared_2816_ = v_isSharedCheck_2852_;
goto v_resetjp_2814_;
}
else
{
lean_dec(v_x_2803_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2852_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_v_2817_; lean_object* v___x_2818_; lean_object* v_xs_x27_2819_; lean_object* v___y_2821_; 
v_v_2817_ = lean_array_fget(v_es_2808_, v_j_2811_);
v___x_2818_ = lean_box(0);
v_xs_x27_2819_ = lean_array_fset(v_es_2808_, v_j_2811_, v___x_2818_);
switch(lean_obj_tag(v_v_2817_))
{
case 0:
{
lean_object* v_key_2826_; lean_object* v_val_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2837_; 
v_key_2826_ = lean_ctor_get(v_v_2817_, 0);
v_val_2827_ = lean_ctor_get(v_v_2817_, 1);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_v_2817_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2829_ = v_v_2817_;
v_isShared_2830_ = v_isSharedCheck_2837_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_val_2827_);
lean_inc(v_key_2826_);
lean_dec(v_v_2817_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2837_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
uint8_t v___x_2831_; 
lean_inc(v_key_2826_);
lean_inc_ref(v_x_2806_);
v___x_2831_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2802_, v_x_2806_, v_key_2826_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_del_object(v___x_2829_);
v___x_2832_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2826_, v_val_2827_, v_x_2806_, v_x_2807_);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
v___y_2821_ = v___x_2833_;
goto v___jp_2820_;
}
else
{
lean_object* v___x_2835_; 
lean_dec(v_val_2827_);
lean_dec(v_key_2826_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 1, v_x_2807_);
lean_ctor_set(v___x_2829_, 0, v_x_2806_);
v___x_2835_ = v___x_2829_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_x_2806_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_x_2807_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
v___y_2821_ = v___x_2835_;
goto v___jp_2820_;
}
}
}
}
case 1:
{
lean_object* v_node_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2850_; 
v_node_2838_ = lean_ctor_get(v_v_2817_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_v_2817_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2840_ = v_v_2817_;
v_isShared_2841_ = v_isSharedCheck_2850_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_node_2838_);
lean_dec(v_v_2817_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2850_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
size_t v___x_2842_; size_t v___x_2843_; size_t v___x_2844_; size_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2842_ = ((size_t)5ULL);
v___x_2843_ = lean_usize_shift_right(v_x_2804_, v___x_2842_);
v___x_2844_ = ((size_t)1ULL);
v___x_2845_ = lean_usize_add(v_x_2805_, v___x_2844_);
v___x_2846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2802_, v_node_2838_, v___x_2843_, v___x_2845_, v_x_2806_, v_x_2807_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2846_);
v___x_2848_ = v___x_2840_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
v___y_2821_ = v___x_2848_;
goto v___jp_2820_;
}
}
}
default: 
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_x_2806_);
lean_ctor_set(v___x_2851_, 1, v_x_2807_);
v___y_2821_ = v___x_2851_;
goto v___jp_2820_;
}
}
v___jp_2820_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = lean_array_fset(v_xs_x27_2819_, v_j_2811_, v___y_2821_);
lean_dec(v_j_2811_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2822_);
v___x_2824_ = v___x_2815_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
else
{
lean_object* v_ks_2854_; lean_object* v_vs_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2873_; 
v_ks_2854_ = lean_ctor_get(v_x_2803_, 0);
v_vs_2855_ = lean_ctor_get(v_x_2803_, 1);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_x_2803_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2857_ = v_x_2803_;
v_isShared_2858_ = v_isSharedCheck_2873_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_vs_2855_);
lean_inc(v_ks_2854_);
lean_dec(v_x_2803_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2873_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_ks_2854_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_vs_2855_);
v___x_2860_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v_newNode_2861_; size_t v___x_2862_; uint8_t v___x_2863_; 
v_newNode_2861_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2802_, v___x_2860_, v_x_2806_, v_x_2807_);
v___x_2862_ = ((size_t)7ULL);
v___x_2863_ = lean_usize_dec_le(v___x_2862_, v_x_2805_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v___x_2864_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2861_);
v___x_2865_ = lean_unsigned_to_nat(4u);
v___x_2866_ = lean_nat_dec_lt(v___x_2864_, v___x_2865_);
lean_dec(v___x_2864_);
if (v___x_2866_ == 0)
{
lean_object* v_ks_2867_; lean_object* v_vs_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_ks_2867_ = lean_ctor_get(v_newNode_2861_, 0);
lean_inc_ref(v_ks_2867_);
v_vs_2868_ = lean_ctor_get(v_newNode_2861_, 1);
lean_inc_ref(v_vs_2868_);
lean_dec_ref(v_newNode_2861_);
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2871_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2802_, v_x_2805_, v_ks_2867_, v_vs_2868_, v___x_2869_, v___x_2870_);
lean_dec_ref(v_vs_2868_);
lean_dec_ref(v_ks_2867_);
return v___x_2871_;
}
else
{
return v_newNode_2861_;
}
}
else
{
return v_newNode_2861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2874_, size_t v_depth_2875_, lean_object* v_keys_2876_, lean_object* v_vals_2877_, lean_object* v_i_2878_, lean_object* v_entries_2879_){
_start:
{
lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2880_ = lean_array_get_size(v_keys_2876_);
v___x_2881_ = lean_nat_dec_lt(v_i_2878_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_dec(v_i_2878_);
return v_entries_2879_;
}
else
{
lean_object* v_k_2882_; lean_object* v_v_2883_; uint64_t v___x_2884_; size_t v_h_2885_; size_t v___x_2886_; lean_object* v___x_2887_; size_t v___x_2888_; size_t v___x_2889_; size_t v___x_2890_; size_t v_h_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_k_2882_ = lean_array_fget_borrowed(v_keys_2876_, v_i_2878_);
v_v_2883_ = lean_array_fget_borrowed(v_vals_2877_, v_i_2878_);
lean_inc_n(v_k_2882_, 2);
v___x_2884_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2874_, v_k_2882_);
v_h_2885_ = lean_uint64_to_usize(v___x_2884_);
v___x_2886_ = ((size_t)5ULL);
v___x_2887_ = lean_unsigned_to_nat(1u);
v___x_2888_ = ((size_t)1ULL);
v___x_2889_ = lean_usize_sub(v_depth_2875_, v___x_2888_);
v___x_2890_ = lean_usize_mul(v___x_2886_, v___x_2889_);
v_h_2891_ = lean_usize_shift_right(v_h_2885_, v___x_2890_);
v___x_2892_ = lean_nat_add(v_i_2878_, v___x_2887_);
lean_dec(v_i_2878_);
lean_inc(v_v_2883_);
v___x_2893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2874_, v_entries_2879_, v_h_2891_, v_depth_2875_, v_k_2882_, v_v_2883_);
v_i_2878_ = v___x_2892_;
v_entries_2879_ = v___x_2893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2895_, lean_object* v_depth_2896_, lean_object* v_keys_2897_, lean_object* v_vals_2898_, lean_object* v_i_2899_, lean_object* v_entries_2900_){
_start:
{
size_t v_depth_boxed_2901_; lean_object* v_res_2902_; 
v_depth_boxed_2901_ = lean_unbox_usize(v_depth_2896_);
lean_dec(v_depth_2896_);
v_res_2902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2895_, v_depth_boxed_2901_, v_keys_2897_, v_vals_2898_, v_i_2899_, v_entries_2900_);
lean_dec_ref(v_vals_2898_);
lean_dec_ref(v_keys_2897_);
lean_dec_ref(v___x_2895_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2903_, lean_object* v_x_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_, lean_object* v_x_2907_, lean_object* v_x_2908_){
_start:
{
size_t v_x_26105__boxed_2909_; size_t v_x_26106__boxed_2910_; lean_object* v_res_2911_; 
v_x_26105__boxed_2909_ = lean_unbox_usize(v_x_2905_);
lean_dec(v_x_2905_);
v_x_26106__boxed_2910_ = lean_unbox_usize(v_x_2906_);
lean_dec(v_x_2906_);
v_res_2911_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2903_, v_x_2904_, v_x_26105__boxed_2909_, v_x_26106__boxed_2910_, v_x_2907_, v_x_2908_);
lean_dec_ref(v___x_2903_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_){
_start:
{
uint64_t v___x_2916_; size_t v___x_2917_; size_t v___x_2918_; lean_object* v___x_2919_; 
lean_inc_ref(v_x_2914_);
v___x_2916_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2912_, v_x_2914_);
v___x_2917_ = lean_uint64_to_usize(v___x_2916_);
v___x_2918_ = ((size_t)1ULL);
v___x_2919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2912_, v_x_2913_, v___x_2917_, v___x_2918_, v_x_2914_, v_x_2915_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2920_, v_x_2921_, v_x_2922_, v_x_2923_);
lean_dec_ref(v___x_2920_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2929_, lean_object* v_rootNew_2930_, uint8_t v_a_2931_, lean_object* v_a_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_snd_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_3110_; 
v_snd_2940_ = lean_ctor_get(v_a_2932_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_a_2932_);
if (v_isSharedCheck_3110_ == 0)
{
lean_object* v_unused_3111_; 
v_unused_3111_ = lean_ctor_get(v_a_2932_, 0);
lean_dec(v_unused_3111_);
v___x_2942_ = v_a_2932_;
v_isShared_2943_ = v_isSharedCheck_3110_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snd_2940_);
lean_dec(v_a_2932_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_3110_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_st_ref_get(v___y_2933_);
lean_inc(v_snd_2940_);
v___x_2946_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2945_, v_snd_2940_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___x_2945_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_3101_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_3101_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_3101_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_self_2951_; lean_object* v_next_2952_; lean_object* v_congr_2953_; lean_object* v_target_x3f_2954_; lean_object* v_proof_x3f_2955_; uint8_t v_flipped_2956_; lean_object* v_size_2957_; uint8_t v_interpreted_2958_; uint8_t v_ctor_2959_; uint8_t v_hasLambdas_2960_; uint8_t v_heqProofs_2961_; lean_object* v_idx_2962_; lean_object* v_generation_2963_; lean_object* v_mt_2964_; lean_object* v_sTerms_2965_; uint8_t v_funCC_2966_; lean_object* v_ematchDiagSource_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3099_; 
v_self_2951_ = lean_ctor_get(v_a_2947_, 0);
v_next_2952_ = lean_ctor_get(v_a_2947_, 1);
v_congr_2953_ = lean_ctor_get(v_a_2947_, 3);
v_target_x3f_2954_ = lean_ctor_get(v_a_2947_, 4);
v_proof_x3f_2955_ = lean_ctor_get(v_a_2947_, 5);
v_flipped_2956_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12);
v_size_2957_ = lean_ctor_get(v_a_2947_, 6);
v_interpreted_2958_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12 + 1);
v_ctor_2959_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12 + 2);
v_hasLambdas_2960_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12 + 3);
v_heqProofs_2961_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12 + 4);
v_idx_2962_ = lean_ctor_get(v_a_2947_, 7);
v_generation_2963_ = lean_ctor_get(v_a_2947_, 8);
v_mt_2964_ = lean_ctor_get(v_a_2947_, 9);
v_sTerms_2965_ = lean_ctor_get(v_a_2947_, 10);
v_funCC_2966_ = lean_ctor_get_uint8(v_a_2947_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2967_ = lean_ctor_get(v_a_2947_, 11);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_a_2947_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v_a_2947_, 2);
lean_dec(v_unused_3100_);
v___x_2969_ = v_a_2947_;
v_isShared_2970_ = v_isSharedCheck_3099_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_ematchDiagSource_2967_);
lean_inc(v_sTerms_2965_);
lean_inc(v_mt_2964_);
lean_inc(v_generation_2963_);
lean_inc(v_idx_2962_);
lean_inc(v_size_2957_);
lean_inc(v_proof_x3f_2955_);
lean_inc(v_target_x3f_2954_);
lean_inc(v_congr_2953_);
lean_inc(v_next_2952_);
lean_inc(v_self_2951_);
lean_dec(v_a_2947_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3099_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___y_2987_; lean_object* v___x_2997_; 
lean_inc(v_ematchDiagSource_2967_);
lean_inc(v_sTerms_2965_);
lean_inc(v_mt_2964_);
lean_inc(v_generation_2963_);
lean_inc(v_idx_2962_);
lean_inc(v_size_2957_);
lean_inc(v_proof_x3f_2955_);
lean_inc(v_target_x3f_2954_);
lean_inc_ref(v_rootNew_2930_);
lean_inc_ref(v_next_2952_);
lean_inc_ref(v_self_2951_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 2, v_rootNew_2930_);
v___x_2997_ = v___x_2969_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_self_2951_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_next_2952_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_rootNew_2930_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_congr_2953_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_target_x3f_2954_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v_proof_x3f_2955_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_size_2957_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v_idx_2962_);
lean_ctor_set(v_reuseFailAlloc_3098_, 8, v_generation_2963_);
lean_ctor_set(v_reuseFailAlloc_3098_, 9, v_mt_2964_);
lean_ctor_set(v_reuseFailAlloc_3098_, 10, v_sTerms_2965_);
lean_ctor_set(v_reuseFailAlloc_3098_, 11, v_ematchDiagSource_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*12, v_flipped_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*12 + 1, v_interpreted_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*12 + 2, v_ctor_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*12 + 3, v_hasLambdas_2960_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*12 + 4, v_heqProofs_2961_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*12 + 5, v_funCC_2966_);
v___x_2997_ = v_reuseFailAlloc_3098_;
goto v_reusejp_2996_;
}
v___jp_2971_:
{
size_t v___x_2972_; size_t v___x_2973_; uint8_t v___x_2974_; 
v___x_2972_ = lean_ptr_addr(v_next_2952_);
v___x_2973_ = lean_ptr_addr(v_lhs_2929_);
v___x_2974_ = lean_usize_dec_eq(v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2976_; 
lean_del_object(v___x_2949_);
lean_dec(v_snd_2940_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v_next_2952_);
lean_ctor_set(v___x_2942_, 0, v___x_2944_);
v___x_2976_ = v___x_2942_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_next_2952_);
v___x_2976_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
v_a_2932_ = v___x_2976_;
goto _start;
}
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2981_; 
lean_dec_ref(v_next_2952_);
lean_dec_ref(v_rootNew_2930_);
v___x_2979_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2979_);
v___x_2981_ = v___x_2942_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_snd_2940_);
v___x_2981_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2983_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2981_);
v___x_2983_ = v___x_2949_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
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
v___jp_2986_:
{
if (lean_obj_tag(v___y_2987_) == 0)
{
lean_dec_ref_known(v___y_2987_, 1);
goto v___jp_2971_;
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref(v_next_2952_);
lean_del_object(v___x_2949_);
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2930_);
v_a_2988_ = lean_ctor_get(v___y_2987_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___y_2987_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___y_2987_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___y_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; 
lean_inc_ref(v___x_2997_);
lean_inc_ref(v_self_2951_);
v___x_2998_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2951_, v___x_2997_, v___y_2933_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_dec_ref_known(v___x_2998_, 1);
if (v_a_2931_ == 0)
{
lean_dec_ref(v___x_2997_);
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
goto v___jp_2971_;
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_2999_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_3000_ = lean_unsigned_to_nat(3u);
v___x_3001_ = l_Lean_Expr_isAppOfArity(v_self_2951_, v___x_2999_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_dec_ref(v___x_2997_);
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
goto v___jp_2971_;
}
else
{
uint8_t v___x_3002_; 
v___x_3002_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_2997_);
lean_dec_ref(v___x_2997_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v_toGoalState_3004_; lean_object* v_enodeMap_3005_; lean_object* v_congrTable_3006_; lean_object* v___x_3007_; 
v___x_3003_ = lean_st_ref_get(v___y_2933_);
v_toGoalState_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc_ref(v_toGoalState_3004_);
lean_dec(v___x_3003_);
v_enodeMap_3005_ = lean_ctor_get(v_toGoalState_3004_, 1);
lean_inc_ref(v_enodeMap_3005_);
v_congrTable_3006_ = lean_ctor_get(v_toGoalState_3004_, 4);
lean_inc_ref(v_congrTable_3006_);
lean_dec_ref(v_toGoalState_3004_);
lean_inc_ref(v_self_2951_);
v___x_3007_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3005_, v_congrTable_3006_, v_self_2951_);
lean_dec_ref(v_congrTable_3006_);
lean_dec_ref(v_enodeMap_3005_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
goto v___jp_2971_;
}
else
{
lean_object* v_val_3008_; lean_object* v_fst_3009_; lean_object* v___x_3010_; 
v_val_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_val_3008_);
lean_dec_ref_known(v___x_3007_, 1);
v_fst_3009_ = lean_ctor_get(v_val_3008_, 0);
lean_inc(v_fst_3009_);
lean_dec(v_val_3008_);
v___x_3010_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3009_, v___y_2934_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; uint8_t v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3012_ = lean_unbox(v_a_3011_);
lean_dec(v_a_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v_toGoalState_3014_; lean_object* v_mvarId_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3089_; 
v___x_3013_ = lean_st_ref_take(v___y_2933_);
v_toGoalState_3014_ = lean_ctor_get(v___x_3013_, 0);
v_mvarId_3015_ = lean_ctor_get(v___x_3013_, 1);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3017_ = v___x_3013_;
v_isShared_3018_ = v_isSharedCheck_3089_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_mvarId_3015_);
lean_inc(v_toGoalState_3014_);
lean_dec(v___x_3013_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3089_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v_nextDeclIdx_3019_; lean_object* v_enodeMap_3020_; lean_object* v_exprs_3021_; lean_object* v_parents_3022_; lean_object* v_congrTable_3023_; lean_object* v_appMap_3024_; lean_object* v_indicesFound_3025_; lean_object* v_newFacts_3026_; uint8_t v_inconsistent_3027_; lean_object* v_nextIdx_3028_; lean_object* v_newRawFacts_3029_; lean_object* v_facts_3030_; lean_object* v_extThms_3031_; lean_object* v_ematch_3032_; lean_object* v_inj_3033_; lean_object* v_split_3034_; lean_object* v_clean_3035_; lean_object* v_sstates_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3088_; 
v_nextDeclIdx_3019_ = lean_ctor_get(v_toGoalState_3014_, 0);
v_enodeMap_3020_ = lean_ctor_get(v_toGoalState_3014_, 1);
v_exprs_3021_ = lean_ctor_get(v_toGoalState_3014_, 2);
v_parents_3022_ = lean_ctor_get(v_toGoalState_3014_, 3);
v_congrTable_3023_ = lean_ctor_get(v_toGoalState_3014_, 4);
v_appMap_3024_ = lean_ctor_get(v_toGoalState_3014_, 5);
v_indicesFound_3025_ = lean_ctor_get(v_toGoalState_3014_, 6);
v_newFacts_3026_ = lean_ctor_get(v_toGoalState_3014_, 7);
v_inconsistent_3027_ = lean_ctor_get_uint8(v_toGoalState_3014_, sizeof(void*)*17);
v_nextIdx_3028_ = lean_ctor_get(v_toGoalState_3014_, 8);
v_newRawFacts_3029_ = lean_ctor_get(v_toGoalState_3014_, 9);
v_facts_3030_ = lean_ctor_get(v_toGoalState_3014_, 10);
v_extThms_3031_ = lean_ctor_get(v_toGoalState_3014_, 11);
v_ematch_3032_ = lean_ctor_get(v_toGoalState_3014_, 12);
v_inj_3033_ = lean_ctor_get(v_toGoalState_3014_, 13);
v_split_3034_ = lean_ctor_get(v_toGoalState_3014_, 14);
v_clean_3035_ = lean_ctor_get(v_toGoalState_3014_, 15);
v_sstates_3036_ = lean_ctor_get(v_toGoalState_3014_, 16);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_toGoalState_3014_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3038_ = v_toGoalState_3014_;
v_isShared_3039_ = v_isSharedCheck_3088_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_sstates_3036_);
lean_inc(v_clean_3035_);
lean_inc(v_split_3034_);
lean_inc(v_inj_3033_);
lean_inc(v_ematch_3032_);
lean_inc(v_extThms_3031_);
lean_inc(v_facts_3030_);
lean_inc(v_newRawFacts_3029_);
lean_inc(v_nextIdx_3028_);
lean_inc(v_newFacts_3026_);
lean_inc(v_indicesFound_3025_);
lean_inc(v_appMap_3024_);
lean_inc(v_congrTable_3023_);
lean_inc(v_parents_3022_);
lean_inc(v_exprs_3021_);
lean_inc(v_enodeMap_3020_);
lean_inc(v_nextDeclIdx_3019_);
lean_dec(v_toGoalState_3014_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3088_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
v___x_3040_ = lean_box(0);
lean_inc_ref(v_self_2951_);
v___x_3041_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3020_, v_congrTable_3023_, v_self_2951_, v___x_3040_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 4, v___x_3041_);
v___x_3043_ = v___x_3038_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_nextDeclIdx_3019_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_enodeMap_3020_);
lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_exprs_3021_);
lean_ctor_set(v_reuseFailAlloc_3087_, 3, v_parents_3022_);
lean_ctor_set(v_reuseFailAlloc_3087_, 4, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3087_, 5, v_appMap_3024_);
lean_ctor_set(v_reuseFailAlloc_3087_, 6, v_indicesFound_3025_);
lean_ctor_set(v_reuseFailAlloc_3087_, 7, v_newFacts_3026_);
lean_ctor_set(v_reuseFailAlloc_3087_, 8, v_nextIdx_3028_);
lean_ctor_set(v_reuseFailAlloc_3087_, 9, v_newRawFacts_3029_);
lean_ctor_set(v_reuseFailAlloc_3087_, 10, v_facts_3030_);
lean_ctor_set(v_reuseFailAlloc_3087_, 11, v_extThms_3031_);
lean_ctor_set(v_reuseFailAlloc_3087_, 12, v_ematch_3032_);
lean_ctor_set(v_reuseFailAlloc_3087_, 13, v_inj_3033_);
lean_ctor_set(v_reuseFailAlloc_3087_, 14, v_split_3034_);
lean_ctor_set(v_reuseFailAlloc_3087_, 15, v_clean_3035_);
lean_ctor_set(v_reuseFailAlloc_3087_, 16, v_sstates_3036_);
lean_ctor_set_uint8(v_reuseFailAlloc_3087_, sizeof(void*)*17, v_inconsistent_3027_);
v___x_3043_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3045_; 
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 0, v___x_3043_);
v___x_3045_ = v___x_3017_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_mvarId_3015_);
v___x_3045_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = lean_st_ref_put(v___y_2933_, v___x_3045_);
lean_inc_ref(v_rootNew_2930_);
lean_inc_ref(v_next_2952_);
lean_inc_ref_n(v_self_2951_, 3);
v___x_3047_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3047_, 0, v_self_2951_);
lean_ctor_set(v___x_3047_, 1, v_next_2952_);
lean_ctor_set(v___x_3047_, 2, v_rootNew_2930_);
lean_ctor_set(v___x_3047_, 3, v_self_2951_);
lean_ctor_set(v___x_3047_, 4, v_target_x3f_2954_);
lean_ctor_set(v___x_3047_, 5, v_proof_x3f_2955_);
lean_ctor_set(v___x_3047_, 6, v_size_2957_);
lean_ctor_set(v___x_3047_, 7, v_idx_2962_);
lean_ctor_set(v___x_3047_, 8, v_generation_2963_);
lean_ctor_set(v___x_3047_, 9, v_mt_2964_);
lean_ctor_set(v___x_3047_, 10, v_sTerms_2965_);
lean_ctor_set(v___x_3047_, 11, v_ematchDiagSource_2967_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*12, v_flipped_2956_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*12 + 1, v_interpreted_2958_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*12 + 2, v_ctor_2959_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*12 + 3, v_hasLambdas_2960_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*12 + 4, v_heqProofs_2961_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*12 + 5, v_funCC_2966_);
v___x_3048_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2951_, v___x_3047_, v___y_2933_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec_ref_known(v___x_3048_, 1);
v___x_3049_ = lean_st_ref_get(v___y_2933_);
lean_inc(v_fst_3009_);
v___x_3050_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3049_, v_fst_3009_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___x_3049_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v_self_3052_; lean_object* v_next_3053_; lean_object* v_root_3054_; lean_object* v_target_x3f_3055_; lean_object* v_proof_x3f_3056_; uint8_t v_flipped_3057_; lean_object* v_size_3058_; uint8_t v_interpreted_3059_; uint8_t v_ctor_3060_; uint8_t v_hasLambdas_3061_; uint8_t v_heqProofs_3062_; lean_object* v_idx_3063_; lean_object* v_generation_3064_; lean_object* v_mt_3065_; lean_object* v_sTerms_3066_; uint8_t v_funCC_3067_; lean_object* v_ematchDiagSource_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3076_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v_self_3052_ = lean_ctor_get(v_a_3051_, 0);
v_next_3053_ = lean_ctor_get(v_a_3051_, 1);
v_root_3054_ = lean_ctor_get(v_a_3051_, 2);
v_target_x3f_3055_ = lean_ctor_get(v_a_3051_, 4);
v_proof_x3f_3056_ = lean_ctor_get(v_a_3051_, 5);
v_flipped_3057_ = lean_ctor_get_uint8(v_a_3051_, sizeof(void*)*12);
v_size_3058_ = lean_ctor_get(v_a_3051_, 6);
v_interpreted_3059_ = lean_ctor_get_uint8(v_a_3051_, sizeof(void*)*12 + 1);
v_ctor_3060_ = lean_ctor_get_uint8(v_a_3051_, sizeof(void*)*12 + 2);
v_hasLambdas_3061_ = lean_ctor_get_uint8(v_a_3051_, sizeof(void*)*12 + 3);
v_heqProofs_3062_ = lean_ctor_get_uint8(v_a_3051_, sizeof(void*)*12 + 4);
v_idx_3063_ = lean_ctor_get(v_a_3051_, 7);
v_generation_3064_ = lean_ctor_get(v_a_3051_, 8);
v_mt_3065_ = lean_ctor_get(v_a_3051_, 9);
v_sTerms_3066_ = lean_ctor_get(v_a_3051_, 10);
v_funCC_3067_ = lean_ctor_get_uint8(v_a_3051_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3068_ = lean_ctor_get(v_a_3051_, 11);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_a_3051_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v_a_3051_, 3);
lean_dec(v_unused_3077_);
v___x_3070_ = v_a_3051_;
v_isShared_3071_ = v_isSharedCheck_3076_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_ematchDiagSource_3068_);
lean_inc(v_sTerms_3066_);
lean_inc(v_mt_3065_);
lean_inc(v_generation_3064_);
lean_inc(v_idx_3063_);
lean_inc(v_size_3058_);
lean_inc(v_proof_x3f_3056_);
lean_inc(v_target_x3f_3055_);
lean_inc(v_root_3054_);
lean_inc(v_next_3053_);
lean_inc(v_self_3052_);
lean_dec(v_a_3051_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3076_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 3, v_self_2951_);
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_self_3052_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_next_3053_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_root_3054_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_self_2951_);
lean_ctor_set(v_reuseFailAlloc_3075_, 4, v_target_x3f_3055_);
lean_ctor_set(v_reuseFailAlloc_3075_, 5, v_proof_x3f_3056_);
lean_ctor_set(v_reuseFailAlloc_3075_, 6, v_size_3058_);
lean_ctor_set(v_reuseFailAlloc_3075_, 7, v_idx_3063_);
lean_ctor_set(v_reuseFailAlloc_3075_, 8, v_generation_3064_);
lean_ctor_set(v_reuseFailAlloc_3075_, 9, v_mt_3065_);
lean_ctor_set(v_reuseFailAlloc_3075_, 10, v_sTerms_3066_);
lean_ctor_set(v_reuseFailAlloc_3075_, 11, v_ematchDiagSource_3068_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12, v_flipped_3057_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12 + 1, v_interpreted_3059_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12 + 2, v_ctor_3060_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12 + 3, v_hasLambdas_3061_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12 + 4, v_heqProofs_3062_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*12 + 5, v_funCC_3067_);
v___x_3073_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3009_, v___x_3073_, v___y_2933_);
v___y_2987_ = v___x_3074_;
goto v___jp_2986_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_fst_3009_);
lean_dec_ref(v_next_2952_);
lean_dec_ref(v_self_2951_);
lean_del_object(v___x_2949_);
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2930_);
v_a_3078_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3050_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3050_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_dec(v_fst_3009_);
lean_dec_ref(v_self_2951_);
v___y_2987_ = v___x_3048_;
goto v___jp_2986_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3009_);
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
goto v___jp_2971_;
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v_fst_3009_);
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_next_2952_);
lean_dec_ref(v_self_2951_);
lean_del_object(v___x_2949_);
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2930_);
v_a_3090_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3010_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3010_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
goto v___jp_2971_;
}
}
}
}
else
{
lean_dec_ref(v___x_2997_);
lean_dec(v_ematchDiagSource_2967_);
lean_dec(v_sTerms_2965_);
lean_dec(v_mt_2964_);
lean_dec(v_generation_2963_);
lean_dec(v_idx_2962_);
lean_dec(v_size_2957_);
lean_dec(v_proof_x3f_2955_);
lean_dec(v_target_x3f_2954_);
lean_dec_ref(v_self_2951_);
v___y_2987_ = v___x_2998_;
goto v___jp_2986_;
}
}
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_del_object(v___x_2942_);
lean_dec(v_snd_2940_);
lean_dec_ref(v_rootNew_2930_);
v_a_3102_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_2946_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_2946_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3112_, lean_object* v_rootNew_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
uint8_t v_a_26289__boxed_3123_; lean_object* v_res_3124_; 
v_a_26289__boxed_3123_ = lean_unbox(v_a_3114_);
v_res_3124_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3112_, v_rootNew_3113_, v_a_26289__boxed_3123_, v_a_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v_lhs_3112_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3125_, lean_object* v_rootNew_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v___x_3138_; 
v___x_3138_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3126_, v_a_3131_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; lean_object* v___x_3143_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3138_, 1);
v___x_3140_ = lean_box(0);
lean_inc_ref(v_lhs_3125_);
v___x_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v_lhs_3125_);
v___x_3142_ = lean_unbox(v_a_3139_);
lean_dec(v_a_3139_);
v___x_3143_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3125_, v_rootNew_3126_, v___x_3142_, v___x_3141_, v_a_3127_, v_a_3131_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
lean_dec_ref(v_lhs_3125_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3157_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3146_ = v___x_3143_;
v_isShared_3147_ = v_isSharedCheck_3157_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3157_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v_fst_3148_; 
v_fst_3148_ = lean_ctor_get(v_a_3144_, 0);
lean_inc(v_fst_3148_);
lean_dec(v_a_3144_);
if (lean_obj_tag(v_fst_3148_) == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3151_; 
v___x_3149_ = lean_box(0);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v___x_3149_);
v___x_3151_ = v___x_3146_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3149_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
else
{
lean_object* v_val_3153_; lean_object* v___x_3155_; 
v_val_3153_ = lean_ctor_get(v_fst_3148_, 0);
lean_inc(v_val_3153_);
lean_dec_ref_known(v_fst_3148_, 1);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v_val_3153_);
v___x_3155_ = v___x_3146_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_val_3153_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
v_a_3158_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3143_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3143_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec_ref(v_rootNew_3126_);
lean_dec_ref(v_lhs_3125_);
v_a_3166_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3138_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3138_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3174_, lean_object* v_rootNew_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3174_, v_rootNew_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_);
lean_dec(v_a_3185_);
lean_dec_ref(v_a_3184_);
lean_dec(v_a_3183_);
lean_dec_ref(v_a_3182_);
lean_dec(v_a_3181_);
lean_dec_ref(v_a_3180_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec(v_a_3176_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3188_, lean_object* v_00_u03b2_3189_, lean_object* v_x_3190_, lean_object* v_x_3191_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3188_, v_x_3190_, v_x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3193_, lean_object* v_00_u03b2_3194_, lean_object* v_x_3195_, lean_object* v_x_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3193_, v_00_u03b2_3194_, v_x_3195_, v_x_3196_);
lean_dec_ref(v_x_3195_);
lean_dec_ref(v___x_3193_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3198_, lean_object* v_00_u03b2_3199_, lean_object* v_x_3200_, lean_object* v_x_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3198_, v_x_3200_, v_x_3201_, v_x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3204_, lean_object* v_00_u03b2_3205_, lean_object* v_x_3206_, lean_object* v_x_3207_, lean_object* v_x_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3204_, v_00_u03b2_3205_, v_x_3206_, v_x_3207_, v_x_3208_);
lean_dec_ref(v___x_3204_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3210_, lean_object* v_rootNew_3211_, uint8_t v_a_3212_, lean_object* v_inst_3213_, lean_object* v_a_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3210_, v_rootNew_3211_, v_a_3212_, v_a_3214_, v___y_3215_, v___y_3219_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3227_, lean_object* v_rootNew_3228_, lean_object* v_a_3229_, lean_object* v_inst_3230_, lean_object* v_a_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
uint8_t v_a_26648__boxed_3243_; lean_object* v_res_3244_; 
v_a_26648__boxed_3243_ = lean_unbox(v_a_3229_);
v_res_3244_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3227_, v_rootNew_3228_, v_a_26648__boxed_3243_, v_inst_3230_, v_a_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v_lhs_3227_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3245_, lean_object* v_00_u03b2_3246_, lean_object* v_x_3247_, size_t v_x_3248_, lean_object* v_x_3249_){
_start:
{
lean_object* v___x_3250_; 
lean_inc_ref(v_x_3247_);
v___x_3250_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3245_, v_x_3247_, v_x_3248_, v_x_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3251_, lean_object* v_00_u03b2_3252_, lean_object* v_x_3253_, lean_object* v_x_3254_, lean_object* v_x_3255_){
_start:
{
size_t v_x_26691__boxed_3256_; lean_object* v_res_3257_; 
v_x_26691__boxed_3256_ = lean_unbox_usize(v_x_3254_);
lean_dec(v_x_3254_);
v_res_3257_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3251_, v_00_u03b2_3252_, v_x_3253_, v_x_26691__boxed_3256_, v_x_3255_);
lean_dec_ref(v_x_3253_);
lean_dec_ref(v___x_3251_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3258_, lean_object* v_00_u03b2_3259_, lean_object* v_x_3260_, size_t v_x_3261_, size_t v_x_3262_, lean_object* v_x_3263_, lean_object* v_x_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3258_, v_x_3260_, v_x_3261_, v_x_3262_, v_x_3263_, v_x_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3266_, lean_object* v_00_u03b2_3267_, lean_object* v_x_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_, lean_object* v_x_3272_){
_start:
{
size_t v_x_26705__boxed_3273_; size_t v_x_26706__boxed_3274_; lean_object* v_res_3275_; 
v_x_26705__boxed_3273_ = lean_unbox_usize(v_x_3269_);
lean_dec(v_x_3269_);
v_x_26706__boxed_3274_ = lean_unbox_usize(v_x_3270_);
lean_dec(v_x_3270_);
v_res_3275_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3266_, v_00_u03b2_3267_, v_x_3268_, v_x_26705__boxed_3273_, v_x_26706__boxed_3274_, v_x_3271_, v_x_3272_);
lean_dec_ref(v___x_3266_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3276_, lean_object* v_00_u03b2_3277_, lean_object* v_keys_3278_, lean_object* v_vals_3279_, lean_object* v_heq_3280_, lean_object* v_i_3281_, lean_object* v_k_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3276_, v_keys_3278_, v_vals_3279_, v_i_3281_, v_k_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3284_, lean_object* v_00_u03b2_3285_, lean_object* v_keys_3286_, lean_object* v_vals_3287_, lean_object* v_heq_3288_, lean_object* v_i_3289_, lean_object* v_k_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3284_, v_00_u03b2_3285_, v_keys_3286_, v_vals_3287_, v_heq_3288_, v_i_3289_, v_k_3290_);
lean_dec_ref(v_vals_3287_);
lean_dec_ref(v_keys_3286_);
lean_dec_ref(v___x_3284_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3292_, lean_object* v_00_u03b2_3293_, lean_object* v_n_3294_, lean_object* v_k_3295_, lean_object* v_v_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3292_, v_n_3294_, v_k_3295_, v_v_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3298_, lean_object* v_00_u03b2_3299_, lean_object* v_n_3300_, lean_object* v_k_3301_, lean_object* v_v_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3298_, v_00_u03b2_3299_, v_n_3300_, v_k_3301_, v_v_3302_);
lean_dec_ref(v___x_3298_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3304_, lean_object* v_00_u03b2_3305_, size_t v_depth_3306_, lean_object* v_keys_3307_, lean_object* v_vals_3308_, lean_object* v_heq_3309_, lean_object* v_i_3310_, lean_object* v_entries_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3304_, v_depth_3306_, v_keys_3307_, v_vals_3308_, v_i_3310_, v_entries_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3313_, lean_object* v_00_u03b2_3314_, lean_object* v_depth_3315_, lean_object* v_keys_3316_, lean_object* v_vals_3317_, lean_object* v_heq_3318_, lean_object* v_i_3319_, lean_object* v_entries_3320_){
_start:
{
size_t v_depth_boxed_3321_; lean_object* v_res_3322_; 
v_depth_boxed_3321_ = lean_unbox_usize(v_depth_3315_);
lean_dec(v_depth_3315_);
v_res_3322_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3313_, v_00_u03b2_3314_, v_depth_boxed_3321_, v_keys_3316_, v_vals_3317_, v_heq_3318_, v_i_3319_, v_entries_3320_);
lean_dec_ref(v_vals_3317_);
lean_dec_ref(v_keys_3316_);
lean_dec_ref(v___x_3313_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3323_, lean_object* v_00_u03b2_3324_, lean_object* v_x_3325_, lean_object* v_x_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3323_, v_x_3325_, v_x_3326_, v_x_3327_, v_x_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3330_, lean_object* v_00_u03b2_3331_, lean_object* v_x_3332_, lean_object* v_x_3333_, lean_object* v_x_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3330_, v_00_u03b2_3331_, v_x_3332_, v_x_3333_, v_x_3334_, v_x_3335_);
lean_dec_ref(v___x_3330_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3337_, lean_object* v_b_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
if (lean_obj_tag(v_as_x27_3337_) == 0)
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_b_3338_);
return v___x_3350_;
}
else
{
lean_object* v_head_3351_; lean_object* v_tail_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_head_3351_ = lean_ctor_get(v_as_x27_3337_, 0);
v_tail_3352_ = lean_ctor_get(v_as_x27_3337_, 1);
v___x_3353_ = lean_box(0);
lean_inc(v_head_3351_);
v___x_3354_ = l_Lean_Meta_Grind_propagateUp(v_head_3351_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_dec_ref_known(v___x_3354_, 1);
v_as_x27_3337_ = v_tail_3352_;
v_b_3338_ = v___x_3353_;
goto _start;
}
else
{
return v___x_3354_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3356_, lean_object* v_b_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3356_, v_b_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec(v_as_x27_3356_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3370_, lean_object* v_b_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
if (lean_obj_tag(v_as_x27_3370_) == 0)
{
lean_object* v___x_3383_; 
v___x_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3383_, 0, v_b_3371_);
return v___x_3383_;
}
else
{
lean_object* v_head_3384_; lean_object* v_tail_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v_head_3384_ = lean_ctor_get(v_as_x27_3370_, 0);
v_tail_3385_ = lean_ctor_get(v_as_x27_3370_, 1);
v___x_3386_ = lean_box(0);
lean_inc(v_head_3384_);
v___x_3387_ = l_Lean_Meta_Grind_propagateDown(v_head_3384_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_dec_ref_known(v___x_3387_, 1);
v_as_x27_3370_ = v_tail_3385_;
v_b_3371_ = v___x_3386_;
goto _start;
}
else
{
return v___x_3387_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3389_, lean_object* v_b_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3389_, v_b_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec(v_as_x27_3389_);
return v_res_3402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v_cls_3406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3407_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3408_ = l_Lean_Name_append(v___x_3407_, v_cls_3406_);
return v___x_3408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3411_ = l_Lean_stringToMessageData(v___x_3410_);
return v___x_3411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3414_ = l_Lean_stringToMessageData(v___x_3413_);
return v___x_3414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3417_ = l_Lean_stringToMessageData(v___x_3416_);
return v___x_3417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3420_ = l_Lean_stringToMessageData(v___x_3419_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3421_, uint8_t v_isHEq_3422_, lean_object* v_lhs_3423_, lean_object* v_rhs_3424_, lean_object* v_lhsNode_3425_, lean_object* v_rhsNode_3426_, lean_object* v_lhsRoot_3427_, lean_object* v_rhsRoot_3428_, uint8_t v_flipped_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; uint8_t v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; uint8_t v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; uint8_t v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; uint8_t v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3559_; lean_object* v___y_3560_; uint8_t v___y_3561_; lean_object* v___y_3562_; uint8_t v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; uint8_t v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; uint8_t v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; uint8_t v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; uint8_t v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; uint8_t v___y_3595_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; uint8_t v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; uint8_t v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v_toCold_3679_; lean_object* v_options_3680_; lean_object* v_inheritedTraceOptions_3681_; uint8_t v_hasTrace_3682_; lean_object* v_cls_3683_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v_fns_u2082_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v_fns_u2081_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; 
v_toCold_3679_ = lean_ctor_get(v_a_3438_, 0);
v_options_3680_ = lean_ctor_get(v_toCold_3679_, 2);
v_inheritedTraceOptions_3681_ = lean_ctor_get(v_toCold_3679_, 11);
v_hasTrace_3682_ = lean_ctor_get_uint8(v_options_3680_, sizeof(void*)*1);
v_cls_3683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3682_ == 0)
{
v___y_3803_ = v_a_3430_;
v___y_3804_ = v_a_3431_;
v___y_3805_ = v_a_3432_;
v___y_3806_ = v_a_3433_;
v___y_3807_ = v_a_3434_;
v___y_3808_ = v_a_3435_;
v___y_3809_ = v_a_3436_;
v___y_3810_ = v_a_3437_;
v___y_3811_ = v_a_3438_;
v___y_3812_ = v_a_3439_;
goto v___jp_3802_;
}
else
{
lean_object* v___x_3883_; uint8_t v___x_3884_; 
v___x_3883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3884_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3681_, v_options_3680_, v___x_3883_);
if (v___x_3884_ == 0)
{
v___y_3803_ = v_a_3430_;
v___y_3804_ = v_a_3431_;
v___y_3805_ = v_a_3432_;
v___y_3806_ = v_a_3433_;
v___y_3807_ = v_a_3434_;
v___y_3808_ = v_a_3435_;
v___y_3809_ = v_a_3436_;
v___y_3810_ = v_a_3437_;
v___y_3811_ = v_a_3438_;
v___y_3812_ = v_a_3439_;
goto v___jp_3802_;
}
else
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_Meta_Grind_updateLastTag(v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v___x_3886_; 
lean_dec_ref_known(v___x_3885_, 1);
lean_inc_ref(v_lhs_3423_);
v___x_3886_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3423_, v_a_3430_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
lean_inc_ref(v_rhs_3424_);
v___x_3888_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3424_, v_a_3430_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3888_, 1);
v___x_3890_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
lean_ctor_set(v___x_3891_, 1, v_a_3887_);
v___x_3892_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3891_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
lean_ctor_set(v___x_3894_, 1, v_a_3889_);
v___x_3895_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3683_, v___x_3894_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_dec_ref_known(v___x_3895_, 1);
v___y_3803_ = v_a_3430_;
v___y_3804_ = v_a_3431_;
v___y_3805_ = v_a_3432_;
v___y_3806_ = v_a_3433_;
v___y_3807_ = v_a_3434_;
v___y_3808_ = v_a_3435_;
v___y_3809_ = v_a_3436_;
v___y_3810_ = v_a_3437_;
v___y_3811_ = v_a_3438_;
v___y_3812_ = v_a_3439_;
goto v___jp_3802_;
}
else
{
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhsNode_3425_);
lean_dec_ref(v_rhs_3424_);
lean_dec_ref(v_lhs_3423_);
lean_dec_ref(v_proof_3421_);
return v___x_3895_;
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec(v_a_3887_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhsNode_3425_);
lean_dec_ref(v_rhs_3424_);
lean_dec_ref(v_lhs_3423_);
lean_dec_ref(v_proof_3421_);
v_a_3896_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3888_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3888_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
else
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhsNode_3425_);
lean_dec_ref(v_rhs_3424_);
lean_dec_ref(v_lhs_3423_);
lean_dec_ref(v_proof_3421_);
v_a_3904_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3886_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3886_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhsNode_3425_);
lean_dec_ref(v_rhs_3424_);
lean_dec_ref(v_lhs_3423_);
lean_dec_ref(v_proof_3421_);
return v___x_3885_;
}
}
}
v___jp_3441_:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3448_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3484_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3461_ = v___x_3458_;
v_isShared_3462_ = v_isSharedCheck_3484_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3484_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
uint8_t v___x_3463_; 
v___x_3463_ = lean_unbox(v_a_3459_);
lean_dec(v_a_3459_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_del_object(v___x_3461_);
v___x_3464_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3442_);
lean_dec(v___y_3442_);
v___x_3465_ = lean_box(0);
v___x_3466_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3464_, v___x_3465_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___x_3464_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3467_; 
lean_dec_ref_known(v___x_3466_, 1);
v___x_3467_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3444_, v___x_3465_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3468_; 
lean_dec_ref_known(v___x_3467_, 1);
v___x_3468_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3446_, v___y_3443_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec_ref(v___y_3443_);
lean_dec_ref(v___y_3446_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v___x_3469_; 
lean_dec_ref_known(v___x_3468_, 1);
v___x_3469_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3445_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3478_; 
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; 
v_unused_3479_ = lean_ctor_get(v___x_3469_, 0);
lean_dec(v_unused_3479_);
v___x_3471_ = v___x_3469_;
v_isShared_3472_ = v_isSharedCheck_3478_;
goto v_resetjp_3470_;
}
else
{
lean_dec(v___x_3469_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3478_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
uint8_t v___x_3473_; 
v___x_3473_ = l_Lean_Expr_isTrue(v___y_3447_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3475_; 
lean_dec(v___y_3444_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3465_);
v___x_3475_ = v___x_3471_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3465_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
else
{
lean_object* v___x_3477_; 
lean_del_object(v___x_3471_);
v___x_3477_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3444_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3444_);
return v___x_3477_;
}
}
}
else
{
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3444_);
return v___x_3469_;
}
}
else
{
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3445_);
lean_dec(v___y_3444_);
return v___x_3468_;
}
}
else
{
lean_dec_ref(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
return v___x_3467_;
}
}
else
{
lean_dec_ref(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
return v___x_3466_;
}
}
else
{
lean_object* v___x_3480_; lean_object* v___x_3482_; 
lean_dec_ref(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
v___x_3480_ = lean_box(0);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v___x_3480_);
v___x_3482_ = v___x_3461_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
v_a_3485_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3458_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3458_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
v___jp_3493_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_inc_ref(v___y_3500_);
v___x_3530_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3530_, 0, v___y_3500_);
lean_ctor_set(v___x_3530_, 1, v___y_3509_);
lean_ctor_set(v___x_3530_, 2, v___y_3499_);
lean_ctor_set(v___x_3530_, 3, v___y_3526_);
lean_ctor_set(v___x_3530_, 4, v___y_3525_);
lean_ctor_set(v___x_3530_, 5, v___y_3495_);
lean_ctor_set(v___x_3530_, 6, v___y_3510_);
lean_ctor_set(v___x_3530_, 7, v___y_3515_);
lean_ctor_set(v___x_3530_, 8, v___y_3498_);
lean_ctor_set(v___x_3530_, 9, v___y_3512_);
lean_ctor_set(v___x_3530_, 10, v___y_3527_);
lean_ctor_set(v___x_3530_, 11, v___y_3521_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*12, v___y_3497_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*12 + 1, v___y_3523_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*12 + 2, v___y_3519_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*12 + 3, v___y_3522_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*12 + 4, v___y_3529_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*12 + 5, v___y_3505_);
lean_inc_ref(v___y_3516_);
v___x_3531_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3516_, v___x_3530_, v___y_3511_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v___x_3532_; 
lean_dec_ref_known(v___x_3531_, 1);
lean_inc_ref(v___y_3503_);
v___x_3532_ = l_Lean_Meta_Grind_propagateBeta(v___y_3503_, v___y_3494_, v___y_3511_, v___y_3506_, v___y_3520_, v___y_3528_, v___y_3508_, v___y_3514_, v___y_3507_, v___y_3517_, v___y_3502_, v___y_3524_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v___x_3533_; 
lean_dec_ref_known(v___x_3532_, 1);
lean_inc_ref(v___y_3496_);
v___x_3533_ = l_Lean_Meta_Grind_propagateBeta(v___y_3496_, v___y_3504_, v___y_3511_, v___y_3506_, v___y_3520_, v___y_3528_, v___y_3508_, v___y_3514_, v___y_3507_, v___y_3517_, v___y_3502_, v___y_3524_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v___x_3534_; 
lean_dec_ref_known(v___x_3533_, 1);
v___x_3534_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3428_, v_lhsRoot_3427_, v___y_3511_, v___y_3507_, v___y_3517_, v___y_3502_, v___y_3524_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
v___x_3536_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3513_, v___y_3511_);
lean_dec_ref(v___y_3513_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v___x_3537_; 
lean_dec_ref_known(v___x_3536_, 1);
lean_inc_ref(v___y_3516_);
v___x_3537_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3518_, v___y_3516_, v___y_3511_, v___y_3506_, v___y_3520_, v___y_3528_, v___y_3508_, v___y_3514_, v___y_3507_, v___y_3517_, v___y_3502_, v___y_3524_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v___x_3538_; 
lean_dec_ref_known(v___x_3537_, 1);
v___x_3538_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3511_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; uint8_t v___x_3540_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref_known(v___x_3538_, 1);
v___x_3540_ = lean_unbox(v_a_3539_);
lean_dec(v_a_3539_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; 
v___x_3541_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3500_, v___y_3511_, v___y_3506_, v___y_3520_, v___y_3528_, v___y_3508_, v___y_3514_, v___y_3507_, v___y_3517_, v___y_3502_, v___y_3524_);
lean_dec_ref(v___y_3500_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_dec_ref_known(v___x_3541_, 1);
v___y_3442_ = v___y_3518_;
v___y_3443_ = v___y_3496_;
v___y_3444_ = v___y_3501_;
v___y_3445_ = v_a_3535_;
v___y_3446_ = v___y_3503_;
v___y_3447_ = v___y_3516_;
v___y_3448_ = v___y_3511_;
v___y_3449_ = v___y_3506_;
v___y_3450_ = v___y_3520_;
v___y_3451_ = v___y_3528_;
v___y_3452_ = v___y_3508_;
v___y_3453_ = v___y_3514_;
v___y_3454_ = v___y_3507_;
v___y_3455_ = v___y_3517_;
v___y_3456_ = v___y_3502_;
v___y_3457_ = v___y_3524_;
goto v___jp_3441_;
}
else
{
lean_dec(v_a_3535_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3496_);
return v___x_3541_;
}
}
else
{
lean_dec_ref(v___y_3500_);
v___y_3442_ = v___y_3518_;
v___y_3443_ = v___y_3496_;
v___y_3444_ = v___y_3501_;
v___y_3445_ = v_a_3535_;
v___y_3446_ = v___y_3503_;
v___y_3447_ = v___y_3516_;
v___y_3448_ = v___y_3511_;
v___y_3449_ = v___y_3506_;
v___y_3450_ = v___y_3520_;
v___y_3451_ = v___y_3528_;
v___y_3452_ = v___y_3508_;
v___y_3453_ = v___y_3514_;
v___y_3454_ = v___y_3507_;
v___y_3455_ = v___y_3517_;
v___y_3456_ = v___y_3502_;
v___y_3457_ = v___y_3524_;
goto v___jp_3441_;
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec(v_a_3535_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v___y_3496_);
v_a_3542_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3538_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3538_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
else
{
lean_dec(v_a_3535_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v___y_3496_);
return v___x_3537_;
}
}
else
{
lean_dec(v_a_3535_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v___y_3496_);
return v___x_3536_;
}
}
else
{
lean_object* v_a_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3557_; 
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v___y_3496_);
v_a_3550_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3552_ = v___x_3534_;
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_a_3550_);
lean_dec(v___x_3534_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3557_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
if (v_isShared_3553_ == 0)
{
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3550_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
else
{
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v___y_3496_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
return v___x_3533_;
}
}
else
{
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v___y_3496_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
return v___x_3532_;
}
}
else
{
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v___y_3496_);
lean_dec_ref(v___y_3494_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
return v___x_3531_;
}
}
v___jp_3558_:
{
if (v_isHEq_3422_ == 0)
{
if (v___y_3561_ == 0)
{
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3562_;
v___y_3497_ = v___y_3563_;
v___y_3498_ = v___y_3564_;
v___y_3499_ = v___y_3565_;
v___y_3500_ = v___y_3566_;
v___y_3501_ = v___y_3567_;
v___y_3502_ = v___y_3568_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3572_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3570_;
v___y_3507_ = v___y_3573_;
v___y_3508_ = v___y_3574_;
v___y_3509_ = v___y_3575_;
v___y_3510_ = v___y_3576_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3583_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3586_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3587_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3595_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3593_;
v___y_3525_ = v___y_3592_;
v___y_3526_ = v___y_3591_;
v___y_3527_ = v___y_3590_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3577_;
goto v___jp_3493_;
}
else
{
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3562_;
v___y_3497_ = v___y_3563_;
v___y_3498_ = v___y_3564_;
v___y_3499_ = v___y_3565_;
v___y_3500_ = v___y_3566_;
v___y_3501_ = v___y_3567_;
v___y_3502_ = v___y_3568_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3572_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3570_;
v___y_3507_ = v___y_3573_;
v___y_3508_ = v___y_3574_;
v___y_3509_ = v___y_3575_;
v___y_3510_ = v___y_3576_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3583_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3586_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3587_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3595_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3593_;
v___y_3525_ = v___y_3592_;
v___y_3526_ = v___y_3591_;
v___y_3527_ = v___y_3590_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3561_;
goto v___jp_3493_;
}
}
else
{
v___y_3494_ = v___y_3559_;
v___y_3495_ = v___y_3560_;
v___y_3496_ = v___y_3562_;
v___y_3497_ = v___y_3563_;
v___y_3498_ = v___y_3564_;
v___y_3499_ = v___y_3565_;
v___y_3500_ = v___y_3566_;
v___y_3501_ = v___y_3567_;
v___y_3502_ = v___y_3568_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3572_;
v___y_3505_ = v___y_3571_;
v___y_3506_ = v___y_3570_;
v___y_3507_ = v___y_3573_;
v___y_3508_ = v___y_3574_;
v___y_3509_ = v___y_3575_;
v___y_3510_ = v___y_3576_;
v___y_3511_ = v___y_3578_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3583_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3586_;
v___y_3519_ = v___y_3585_;
v___y_3520_ = v___y_3587_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3595_;
v___y_3523_ = v___y_3589_;
v___y_3524_ = v___y_3593_;
v___y_3525_ = v___y_3592_;
v___y_3526_ = v___y_3591_;
v___y_3527_ = v___y_3590_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v_isHEq_3422_;
goto v___jp_3493_;
}
}
v___jp_3596_:
{
lean_object* v___x_3619_; 
v___x_3619_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3600_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
if (lean_obj_tag(v___x_3619_) == 0)
{
uint8_t v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
lean_dec_ref_known(v___x_3619_, 1);
v___x_3620_ = 0;
v___x_3621_ = lean_st_ref_get(v___y_3609_);
v___x_3622_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3621_, v_lhs_3423_, v___x_3620_);
lean_dec(v___x_3621_);
v___x_3623_ = lean_st_ref_get(v___y_3609_);
lean_inc_ref(v___y_3604_);
v___x_3624_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3623_, v___y_3604_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___x_3623_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v_self_3626_; lean_object* v_root_3627_; lean_object* v_congr_3628_; lean_object* v_target_x3f_3629_; lean_object* v_proof_x3f_3630_; uint8_t v_flipped_3631_; lean_object* v_size_3632_; uint8_t v_interpreted_3633_; uint8_t v_ctor_3634_; uint8_t v_hasLambdas_3635_; uint8_t v_heqProofs_3636_; lean_object* v_idx_3637_; lean_object* v_generation_3638_; lean_object* v_mt_3639_; lean_object* v_sTerms_3640_; uint8_t v_funCC_3641_; lean_object* v_ematchDiagSource_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3669_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v_self_3626_ = lean_ctor_get(v_a_3625_, 0);
v_root_3627_ = lean_ctor_get(v_a_3625_, 2);
v_congr_3628_ = lean_ctor_get(v_a_3625_, 3);
v_target_x3f_3629_ = lean_ctor_get(v_a_3625_, 4);
v_proof_x3f_3630_ = lean_ctor_get(v_a_3625_, 5);
v_flipped_3631_ = lean_ctor_get_uint8(v_a_3625_, sizeof(void*)*12);
v_size_3632_ = lean_ctor_get(v_a_3625_, 6);
v_interpreted_3633_ = lean_ctor_get_uint8(v_a_3625_, sizeof(void*)*12 + 1);
v_ctor_3634_ = lean_ctor_get_uint8(v_a_3625_, sizeof(void*)*12 + 2);
v_hasLambdas_3635_ = lean_ctor_get_uint8(v_a_3625_, sizeof(void*)*12 + 3);
v_heqProofs_3636_ = lean_ctor_get_uint8(v_a_3625_, sizeof(void*)*12 + 4);
v_idx_3637_ = lean_ctor_get(v_a_3625_, 7);
v_generation_3638_ = lean_ctor_get(v_a_3625_, 8);
v_mt_3639_ = lean_ctor_get(v_a_3625_, 9);
v_sTerms_3640_ = lean_ctor_get(v_a_3625_, 10);
v_funCC_3641_ = lean_ctor_get_uint8(v_a_3625_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3642_ = lean_ctor_get(v_a_3625_, 11);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_a_3625_);
if (v_isSharedCheck_3669_ == 0)
{
lean_object* v_unused_3670_; 
v_unused_3670_ = lean_ctor_get(v_a_3625_, 1);
lean_dec(v_unused_3670_);
v___x_3644_ = v_a_3625_;
v_isShared_3645_ = v_isSharedCheck_3669_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_ematchDiagSource_3642_);
lean_inc(v_sTerms_3640_);
lean_inc(v_mt_3639_);
lean_inc(v_generation_3638_);
lean_inc(v_idx_3637_);
lean_inc(v_size_3632_);
lean_inc(v_proof_x3f_3630_);
lean_inc(v_target_x3f_3629_);
lean_inc(v_congr_3628_);
lean_inc(v_root_3627_);
lean_inc(v_self_3626_);
lean_dec(v_a_3625_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3669_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v_self_3646_; lean_object* v_next_3647_; lean_object* v_root_3648_; lean_object* v_congr_3649_; lean_object* v_target_x3f_3650_; lean_object* v_proof_x3f_3651_; uint8_t v_flipped_3652_; lean_object* v_size_3653_; uint8_t v_interpreted_3654_; uint8_t v_ctor_3655_; uint8_t v_hasLambdas_3656_; uint8_t v_heqProofs_3657_; lean_object* v_idx_3658_; lean_object* v_generation_3659_; lean_object* v_mt_3660_; lean_object* v_sTerms_3661_; uint8_t v_funCC_3662_; lean_object* v_ematchDiagSource_3663_; lean_object* v___x_3665_; 
v_self_3646_ = lean_ctor_get(v_rhsRoot_3428_, 0);
v_next_3647_ = lean_ctor_get(v_rhsRoot_3428_, 1);
v_root_3648_ = lean_ctor_get(v_rhsRoot_3428_, 2);
v_congr_3649_ = lean_ctor_get(v_rhsRoot_3428_, 3);
v_target_x3f_3650_ = lean_ctor_get(v_rhsRoot_3428_, 4);
v_proof_x3f_3651_ = lean_ctor_get(v_rhsRoot_3428_, 5);
v_flipped_3652_ = lean_ctor_get_uint8(v_rhsRoot_3428_, sizeof(void*)*12);
v_size_3653_ = lean_ctor_get(v_rhsRoot_3428_, 6);
v_interpreted_3654_ = lean_ctor_get_uint8(v_rhsRoot_3428_, sizeof(void*)*12 + 1);
v_ctor_3655_ = lean_ctor_get_uint8(v_rhsRoot_3428_, sizeof(void*)*12 + 2);
v_hasLambdas_3656_ = lean_ctor_get_uint8(v_rhsRoot_3428_, sizeof(void*)*12 + 3);
v_heqProofs_3657_ = lean_ctor_get_uint8(v_rhsRoot_3428_, sizeof(void*)*12 + 4);
v_idx_3658_ = lean_ctor_get(v_rhsRoot_3428_, 7);
v_generation_3659_ = lean_ctor_get(v_rhsRoot_3428_, 8);
v_mt_3660_ = lean_ctor_get(v_rhsRoot_3428_, 9);
v_sTerms_3661_ = lean_ctor_get(v_rhsRoot_3428_, 10);
v_funCC_3662_ = lean_ctor_get_uint8(v_rhsRoot_3428_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3663_ = lean_ctor_get(v_rhsRoot_3428_, 11);
lean_inc_ref(v_next_3647_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 1, v_next_3647_);
v___x_3665_ = v___x_3644_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_self_3626_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_next_3647_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_root_3627_);
lean_ctor_set(v_reuseFailAlloc_3668_, 3, v_congr_3628_);
lean_ctor_set(v_reuseFailAlloc_3668_, 4, v_target_x3f_3629_);
lean_ctor_set(v_reuseFailAlloc_3668_, 5, v_proof_x3f_3630_);
lean_ctor_set(v_reuseFailAlloc_3668_, 6, v_size_3632_);
lean_ctor_set(v_reuseFailAlloc_3668_, 7, v_idx_3637_);
lean_ctor_set(v_reuseFailAlloc_3668_, 8, v_generation_3638_);
lean_ctor_set(v_reuseFailAlloc_3668_, 9, v_mt_3639_);
lean_ctor_set(v_reuseFailAlloc_3668_, 10, v_sTerms_3640_);
lean_ctor_set(v_reuseFailAlloc_3668_, 11, v_ematchDiagSource_3642_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, sizeof(void*)*12, v_flipped_3631_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, sizeof(void*)*12 + 1, v_interpreted_3633_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, sizeof(void*)*12 + 2, v_ctor_3634_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, sizeof(void*)*12 + 3, v_hasLambdas_3635_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, sizeof(void*)*12 + 4, v_heqProofs_3636_);
lean_ctor_set_uint8(v_reuseFailAlloc_3668_, sizeof(void*)*12 + 5, v_funCC_3641_);
v___x_3665_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3605_, v___x_3665_, v___y_3609_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v___x_3667_; 
lean_dec_ref_known(v___x_3666_, 1);
v___x_3667_ = lean_nat_add(v_size_3653_, v___y_3599_);
lean_dec(v___y_3599_);
if (v_hasLambdas_3656_ == 0)
{
lean_inc(v_target_x3f_3650_);
lean_inc_ref(v_congr_3649_);
lean_inc(v_sTerms_3661_);
lean_inc(v_ematchDiagSource_3663_);
lean_inc(v_idx_3658_);
lean_inc(v_mt_3660_);
lean_inc_ref(v_self_3646_);
lean_inc_ref(v_root_3648_);
lean_inc(v_generation_3659_);
lean_inc(v_proof_x3f_3651_);
v___y_3559_ = v___y_3598_;
v___y_3560_ = v_proof_x3f_3651_;
v___y_3561_ = v_heqProofs_3657_;
v___y_3562_ = v___y_3602_;
v___y_3563_ = v_flipped_3652_;
v___y_3564_ = v_generation_3659_;
v___y_3565_ = v_root_3648_;
v___y_3566_ = v_self_3646_;
v___y_3567_ = v___x_3622_;
v___y_3568_ = v___y_3617_;
v___y_3569_ = v___y_3603_;
v___y_3570_ = v___y_3610_;
v___y_3571_ = v_funCC_3662_;
v___y_3572_ = v___y_3607_;
v___y_3573_ = v___y_3615_;
v___y_3574_ = v___y_3613_;
v___y_3575_ = v___y_3597_;
v___y_3576_ = v___x_3667_;
v___y_3577_ = v___y_3601_;
v___y_3578_ = v___y_3609_;
v___y_3579_ = v_mt_3660_;
v___y_3580_ = v___y_3604_;
v___y_3581_ = v___y_3614_;
v___y_3582_ = v_idx_3658_;
v___y_3583_ = v___y_3608_;
v___y_3584_ = v___y_3616_;
v___y_3585_ = v_ctor_3655_;
v___y_3586_ = v___y_3600_;
v___y_3587_ = v___y_3611_;
v___y_3588_ = v_ematchDiagSource_3663_;
v___y_3589_ = v_interpreted_3654_;
v___y_3590_ = v_sTerms_3661_;
v___y_3591_ = v_congr_3649_;
v___y_3592_ = v_target_x3f_3650_;
v___y_3593_ = v___y_3618_;
v___y_3594_ = v___y_3612_;
v___y_3595_ = v___y_3606_;
goto v___jp_3558_;
}
else
{
lean_inc(v_target_x3f_3650_);
lean_inc_ref(v_congr_3649_);
lean_inc(v_sTerms_3661_);
lean_inc(v_ematchDiagSource_3663_);
lean_inc(v_idx_3658_);
lean_inc(v_mt_3660_);
lean_inc_ref(v_self_3646_);
lean_inc_ref(v_root_3648_);
lean_inc(v_generation_3659_);
lean_inc(v_proof_x3f_3651_);
v___y_3559_ = v___y_3598_;
v___y_3560_ = v_proof_x3f_3651_;
v___y_3561_ = v_heqProofs_3657_;
v___y_3562_ = v___y_3602_;
v___y_3563_ = v_flipped_3652_;
v___y_3564_ = v_generation_3659_;
v___y_3565_ = v_root_3648_;
v___y_3566_ = v_self_3646_;
v___y_3567_ = v___x_3622_;
v___y_3568_ = v___y_3617_;
v___y_3569_ = v___y_3603_;
v___y_3570_ = v___y_3610_;
v___y_3571_ = v_funCC_3662_;
v___y_3572_ = v___y_3607_;
v___y_3573_ = v___y_3615_;
v___y_3574_ = v___y_3613_;
v___y_3575_ = v___y_3597_;
v___y_3576_ = v___x_3667_;
v___y_3577_ = v___y_3601_;
v___y_3578_ = v___y_3609_;
v___y_3579_ = v_mt_3660_;
v___y_3580_ = v___y_3604_;
v___y_3581_ = v___y_3614_;
v___y_3582_ = v_idx_3658_;
v___y_3583_ = v___y_3608_;
v___y_3584_ = v___y_3616_;
v___y_3585_ = v_ctor_3655_;
v___y_3586_ = v___y_3600_;
v___y_3587_ = v___y_3611_;
v___y_3588_ = v_ematchDiagSource_3663_;
v___y_3589_ = v_interpreted_3654_;
v___y_3590_ = v_sTerms_3661_;
v___y_3591_ = v_congr_3649_;
v___y_3592_ = v_target_x3f_3650_;
v___y_3593_ = v___y_3618_;
v___y_3594_ = v___y_3612_;
v___y_3595_ = v_hasLambdas_3656_;
goto v___jp_3558_;
}
}
else
{
lean_dec(v___x_3622_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
return v___x_3666_;
}
}
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_dec(v___x_3622_);
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
v_a_3671_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3624_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3624_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
else
{
lean_dec_ref(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_lhs_3423_);
return v___x_3619_;
}
}
v___jp_3684_:
{
lean_object* v_self_3700_; lean_object* v_next_3701_; lean_object* v_size_3702_; uint8_t v_hasLambdas_3703_; uint8_t v_heqProofs_3704_; lean_object* v___x_3705_; 
v_self_3700_ = lean_ctor_get(v_lhsRoot_3427_, 0);
v_next_3701_ = lean_ctor_get(v_lhsRoot_3427_, 1);
v_size_3702_ = lean_ctor_get(v_lhsRoot_3427_, 6);
v_hasLambdas_3703_ = lean_ctor_get_uint8(v_lhsRoot_3427_, sizeof(void*)*12 + 3);
v_heqProofs_3704_ = lean_ctor_get_uint8(v_lhsRoot_3427_, sizeof(void*)*12 + 4);
v___x_3705_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3700_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v_root_3707_; lean_object* v___x_3708_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref_known(v___x_3705_, 1);
v_root_3707_ = lean_ctor_get(v_rhsNode_3426_, 2);
lean_inc_ref_n(v_root_3707_, 2);
lean_dec_ref(v_rhsNode_3426_);
lean_inc_ref(v_lhs_3423_);
v___x_3708_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3423_, v_root_3707_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_toCold_3709_; lean_object* v_options_3710_; uint8_t v_hasTrace_3711_; 
lean_dec_ref_known(v___x_3708_, 1);
v_toCold_3709_ = lean_ctor_get(v___y_3698_, 0);
v_options_3710_ = lean_ctor_get(v_toCold_3709_, 2);
v_hasTrace_3711_ = lean_ctor_get_uint8(v_options_3710_, sizeof(void*)*1);
if (v_hasTrace_3711_ == 0)
{
lean_inc_ref(v_self_3700_);
lean_inc(v_size_3702_);
lean_inc_ref(v_next_3701_);
v___y_3597_ = v_next_3701_;
v___y_3598_ = v___y_3685_;
v___y_3599_ = v_size_3702_;
v___y_3600_ = v_a_3706_;
v___y_3601_ = v_heqProofs_3704_;
v___y_3602_ = v___y_3686_;
v___y_3603_ = v___y_3687_;
v___y_3604_ = v_self_3700_;
v___y_3605_ = v___y_3688_;
v___y_3606_ = v_hasLambdas_3703_;
v___y_3607_ = v_fns_u2082_3689_;
v___y_3608_ = v_root_3707_;
v___y_3609_ = v___y_3690_;
v___y_3610_ = v___y_3691_;
v___y_3611_ = v___y_3692_;
v___y_3612_ = v___y_3693_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v___y_3695_;
v___y_3615_ = v___y_3696_;
v___y_3616_ = v___y_3697_;
v___y_3617_ = v___y_3698_;
v___y_3618_ = v___y_3699_;
goto v___jp_3596_;
}
else
{
lean_object* v_inheritedTraceOptions_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v_inheritedTraceOptions_3712_ = lean_ctor_get(v_toCold_3709_, 11);
v___x_3713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3714_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3712_, v_options_3710_, v___x_3713_);
if (v___x_3714_ == 0)
{
lean_inc_ref(v_self_3700_);
lean_inc(v_size_3702_);
lean_inc_ref(v_next_3701_);
v___y_3597_ = v_next_3701_;
v___y_3598_ = v___y_3685_;
v___y_3599_ = v_size_3702_;
v___y_3600_ = v_a_3706_;
v___y_3601_ = v_heqProofs_3704_;
v___y_3602_ = v___y_3686_;
v___y_3603_ = v___y_3687_;
v___y_3604_ = v_self_3700_;
v___y_3605_ = v___y_3688_;
v___y_3606_ = v_hasLambdas_3703_;
v___y_3607_ = v_fns_u2082_3689_;
v___y_3608_ = v_root_3707_;
v___y_3609_ = v___y_3690_;
v___y_3610_ = v___y_3691_;
v___y_3611_ = v___y_3692_;
v___y_3612_ = v___y_3693_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v___y_3695_;
v___y_3615_ = v___y_3696_;
v___y_3616_ = v___y_3697_;
v___y_3617_ = v___y_3698_;
v___y_3618_ = v___y_3699_;
goto v___jp_3596_;
}
else
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Meta_Grind_updateLastTag(v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v___x_3716_; 
lean_dec_ref_known(v___x_3715_, 1);
lean_inc_ref(v_lhs_3423_);
v___x_3716_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3423_, v___y_3690_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3718_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref_known(v___x_3716_, 1);
lean_inc_ref(v_root_3707_);
v___x_3718_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3707_, v___y_3690_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v___x_3720_ = lean_st_ref_get(v___y_3690_);
lean_inc_ref(v_lhs_3423_);
v___x_3721_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3720_, v_lhs_3423_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___x_3720_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3723_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
v___x_3723_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3722_, v___y_3690_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref_known(v___x_3723_, 1);
v___x_3725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3726_, 0, v_a_3717_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
lean_ctor_set(v___x_3727_, 1, v_a_3719_);
v___x_3728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
lean_ctor_set(v___x_3730_, 1, v_a_3724_);
v___x_3731_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3683_, v___x_3730_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_dec_ref_known(v___x_3731_, 1);
lean_inc_ref(v_self_3700_);
lean_inc(v_size_3702_);
lean_inc_ref(v_next_3701_);
v___y_3597_ = v_next_3701_;
v___y_3598_ = v___y_3685_;
v___y_3599_ = v_size_3702_;
v___y_3600_ = v_a_3706_;
v___y_3601_ = v_heqProofs_3704_;
v___y_3602_ = v___y_3686_;
v___y_3603_ = v___y_3687_;
v___y_3604_ = v_self_3700_;
v___y_3605_ = v___y_3688_;
v___y_3606_ = v_hasLambdas_3703_;
v___y_3607_ = v_fns_u2082_3689_;
v___y_3608_ = v_root_3707_;
v___y_3609_ = v___y_3690_;
v___y_3610_ = v___y_3691_;
v___y_3611_ = v___y_3692_;
v___y_3612_ = v___y_3693_;
v___y_3613_ = v___y_3694_;
v___y_3614_ = v___y_3695_;
v___y_3615_ = v___y_3696_;
v___y_3616_ = v___y_3697_;
v___y_3617_ = v___y_3698_;
v___y_3618_ = v___y_3699_;
goto v___jp_3596_;
}
else
{
lean_dec_ref(v_root_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_fns_u2082_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_lhs_3423_);
return v___x_3731_;
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec(v_a_3719_);
lean_dec(v_a_3717_);
lean_dec_ref(v_root_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_fns_u2082_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_lhs_3423_);
v_a_3732_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3723_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3723_);
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
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec(v_a_3719_);
lean_dec(v_a_3717_);
lean_dec_ref(v_root_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_fns_u2082_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_lhs_3423_);
v_a_3740_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3721_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3721_);
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
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec(v_a_3717_);
lean_dec_ref(v_root_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_fns_u2082_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_lhs_3423_);
v_a_3748_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3718_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3718_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec_ref(v_root_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_fns_u2082_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_lhs_3423_);
v_a_3756_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3716_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3716_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
else
{
lean_dec_ref(v_root_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_fns_u2082_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_lhs_3423_);
return v___x_3715_;
}
}
}
}
else
{
lean_dec_ref(v_root_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_fns_u2082_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_lhs_3423_);
return v___x_3708_;
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec_ref(v_fns_u2082_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhs_3423_);
v_a_3764_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3705_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3705_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
v___jp_3772_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v___x_3787_ = lean_array_get_size(v___y_3773_);
v___x_3788_ = lean_unsigned_to_nat(0u);
v___x_3789_ = lean_nat_dec_eq(v___x_3787_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_object* v_self_3790_; lean_object* v___x_3791_; 
v_self_3790_ = lean_ctor_get(v_lhsRoot_3427_, 0);
lean_inc_ref(v_self_3790_);
v___x_3791_ = l_Lean_Meta_Grind_getFnRoots(v_self_3790_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___y_3685_ = v_fns_u2081_3776_;
v___y_3686_ = v___y_3773_;
v___y_3687_ = v___y_3774_;
v___y_3688_ = v___y_3775_;
v_fns_u2082_3689_ = v_a_3792_;
v___y_3690_ = v___y_3777_;
v___y_3691_ = v___y_3778_;
v___y_3692_ = v___y_3779_;
v___y_3693_ = v___y_3780_;
v___y_3694_ = v___y_3781_;
v___y_3695_ = v___y_3782_;
v___y_3696_ = v___y_3783_;
v___y_3697_ = v___y_3784_;
v___y_3698_ = v___y_3785_;
v___y_3699_ = v___y_3786_;
goto v___jp_3684_;
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec_ref(v_fns_u2081_3776_);
lean_dec_ref(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhs_3423_);
v_a_3793_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3791_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3791_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
else
{
lean_object* v___x_3801_; 
v___x_3801_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3685_ = v_fns_u2081_3776_;
v___y_3686_ = v___y_3773_;
v___y_3687_ = v___y_3774_;
v___y_3688_ = v___y_3775_;
v_fns_u2082_3689_ = v___x_3801_;
v___y_3690_ = v___y_3777_;
v___y_3691_ = v___y_3778_;
v___y_3692_ = v___y_3779_;
v___y_3693_ = v___y_3780_;
v___y_3694_ = v___y_3781_;
v___y_3695_ = v___y_3782_;
v___y_3696_ = v___y_3783_;
v___y_3697_ = v___y_3784_;
v___y_3698_ = v___y_3785_;
v___y_3699_ = v___y_3786_;
goto v___jp_3684_;
}
}
v___jp_3802_:
{
lean_object* v___x_3813_; 
lean_inc_ref(v_lhs_3423_);
v___x_3813_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3423_, v___y_3803_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3881_; 
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3881_ == 0)
{
lean_object* v_unused_3882_; 
v_unused_3882_ = lean_ctor_get(v___x_3813_, 0);
lean_dec(v_unused_3882_);
v___x_3815_ = v___x_3813_;
v_isShared_3816_ = v_isSharedCheck_3881_;
goto v_resetjp_3814_;
}
else
{
lean_dec(v___x_3813_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3881_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v_self_3817_; lean_object* v_next_3818_; lean_object* v_root_3819_; lean_object* v_congr_3820_; lean_object* v_size_3821_; uint8_t v_interpreted_3822_; uint8_t v_ctor_3823_; uint8_t v_hasLambdas_3824_; uint8_t v_heqProofs_3825_; lean_object* v_idx_3826_; lean_object* v_generation_3827_; lean_object* v_mt_3828_; lean_object* v_sTerms_3829_; uint8_t v_funCC_3830_; lean_object* v_ematchDiagSource_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3878_; 
v_self_3817_ = lean_ctor_get(v_lhsNode_3425_, 0);
v_next_3818_ = lean_ctor_get(v_lhsNode_3425_, 1);
v_root_3819_ = lean_ctor_get(v_lhsNode_3425_, 2);
v_congr_3820_ = lean_ctor_get(v_lhsNode_3425_, 3);
v_size_3821_ = lean_ctor_get(v_lhsNode_3425_, 6);
v_interpreted_3822_ = lean_ctor_get_uint8(v_lhsNode_3425_, sizeof(void*)*12 + 1);
v_ctor_3823_ = lean_ctor_get_uint8(v_lhsNode_3425_, sizeof(void*)*12 + 2);
v_hasLambdas_3824_ = lean_ctor_get_uint8(v_lhsNode_3425_, sizeof(void*)*12 + 3);
v_heqProofs_3825_ = lean_ctor_get_uint8(v_lhsNode_3425_, sizeof(void*)*12 + 4);
v_idx_3826_ = lean_ctor_get(v_lhsNode_3425_, 7);
v_generation_3827_ = lean_ctor_get(v_lhsNode_3425_, 8);
v_mt_3828_ = lean_ctor_get(v_lhsNode_3425_, 9);
v_sTerms_3829_ = lean_ctor_get(v_lhsNode_3425_, 10);
v_funCC_3830_ = lean_ctor_get_uint8(v_lhsNode_3425_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3831_ = lean_ctor_get(v_lhsNode_3425_, 11);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_lhsNode_3425_);
if (v_isSharedCheck_3878_ == 0)
{
lean_object* v_unused_3879_; lean_object* v_unused_3880_; 
v_unused_3879_ = lean_ctor_get(v_lhsNode_3425_, 5);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_lhsNode_3425_, 4);
lean_dec(v_unused_3880_);
v___x_3833_ = v_lhsNode_3425_;
v_isShared_3834_ = v_isSharedCheck_3878_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_ematchDiagSource_3831_);
lean_inc(v_sTerms_3829_);
lean_inc(v_mt_3828_);
lean_inc(v_generation_3827_);
lean_inc(v_idx_3826_);
lean_inc(v_size_3821_);
lean_inc(v_congr_3820_);
lean_inc(v_root_3819_);
lean_inc(v_next_3818_);
lean_inc(v_self_3817_);
lean_dec(v_lhsNode_3425_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3878_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3816_ == 0)
{
lean_ctor_set_tag(v___x_3815_, 1);
lean_ctor_set(v___x_3815_, 0, v_rhs_3424_);
v___x_3836_ = v___x_3815_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_rhs_3424_);
v___x_3836_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3837_; lean_object* v___x_3839_; 
v___x_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3837_, 0, v_proof_3421_);
lean_inc_ref(v_root_3819_);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 5, v___x_3837_);
lean_ctor_set(v___x_3833_, 4, v___x_3836_);
v___x_3839_ = v___x_3833_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_self_3817_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_next_3818_);
lean_ctor_set(v_reuseFailAlloc_3876_, 2, v_root_3819_);
lean_ctor_set(v_reuseFailAlloc_3876_, 3, v_congr_3820_);
lean_ctor_set(v_reuseFailAlloc_3876_, 4, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3876_, 5, v___x_3837_);
lean_ctor_set(v_reuseFailAlloc_3876_, 6, v_size_3821_);
lean_ctor_set(v_reuseFailAlloc_3876_, 7, v_idx_3826_);
lean_ctor_set(v_reuseFailAlloc_3876_, 8, v_generation_3827_);
lean_ctor_set(v_reuseFailAlloc_3876_, 9, v_mt_3828_);
lean_ctor_set(v_reuseFailAlloc_3876_, 10, v_sTerms_3829_);
lean_ctor_set(v_reuseFailAlloc_3876_, 11, v_ematchDiagSource_3831_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, sizeof(void*)*12 + 1, v_interpreted_3822_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, sizeof(void*)*12 + 2, v_ctor_3823_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, sizeof(void*)*12 + 3, v_hasLambdas_3824_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, sizeof(void*)*12 + 4, v_heqProofs_3825_);
lean_ctor_set_uint8(v_reuseFailAlloc_3876_, sizeof(void*)*12 + 5, v_funCC_3830_);
v___x_3839_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3840_; 
lean_ctor_set_uint8(v___x_3839_, sizeof(void*)*12, v_flipped_3429_);
lean_inc_ref(v_lhs_3423_);
v___x_3840_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3423_, v___x_3839_, v___y_3803_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v___x_3841_; 
lean_dec_ref_known(v___x_3840_, 1);
v___x_3841_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3427_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; lean_object* v___x_3843_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v___x_3841_, 1);
v___x_3843_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3428_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref_known(v___x_3843_, 1);
v___x_3845_ = lean_array_get_size(v_a_3842_);
v___x_3846_ = lean_unsigned_to_nat(0u);
v___x_3847_ = lean_nat_dec_eq(v___x_3845_, v___x_3846_);
if (v___x_3847_ == 0)
{
lean_object* v_self_3848_; lean_object* v___x_3849_; 
v_self_3848_ = lean_ctor_get(v_rhsRoot_3428_, 0);
lean_inc_ref(v_self_3848_);
v___x_3849_ = l_Lean_Meta_Grind_getFnRoots(v_self_3848_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
v___y_3773_ = v_a_3844_;
v___y_3774_ = v_a_3842_;
v___y_3775_ = v_root_3819_;
v_fns_u2081_3776_ = v_a_3850_;
v___y_3777_ = v___y_3803_;
v___y_3778_ = v___y_3804_;
v___y_3779_ = v___y_3805_;
v___y_3780_ = v___y_3806_;
v___y_3781_ = v___y_3807_;
v___y_3782_ = v___y_3808_;
v___y_3783_ = v___y_3809_;
v___y_3784_ = v___y_3810_;
v___y_3785_ = v___y_3811_;
v___y_3786_ = v___y_3812_;
goto v___jp_3772_;
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_dec(v_a_3844_);
lean_dec(v_a_3842_);
lean_dec_ref(v_root_3819_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhs_3423_);
v_a_3851_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3849_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3849_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_object* v___x_3859_; 
v___x_3859_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3773_ = v_a_3844_;
v___y_3774_ = v_a_3842_;
v___y_3775_ = v_root_3819_;
v_fns_u2081_3776_ = v___x_3859_;
v___y_3777_ = v___y_3803_;
v___y_3778_ = v___y_3804_;
v___y_3779_ = v___y_3805_;
v___y_3780_ = v___y_3806_;
v___y_3781_ = v___y_3807_;
v___y_3782_ = v___y_3808_;
v___y_3783_ = v___y_3809_;
v___y_3784_ = v___y_3810_;
v___y_3785_ = v___y_3811_;
v___y_3786_ = v___y_3812_;
goto v___jp_3772_;
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_a_3842_);
lean_dec_ref(v_root_3819_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhs_3423_);
v_a_3860_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3843_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3843_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec_ref(v_root_3819_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhs_3423_);
v_a_3868_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3841_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3841_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
lean_dec_ref(v_root_3819_);
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhs_3423_);
return v___x_3840_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3428_);
lean_dec_ref(v_lhsRoot_3427_);
lean_dec_ref(v_rhsNode_3426_);
lean_dec_ref(v_lhsNode_3425_);
lean_dec_ref(v_rhs_3424_);
lean_dec_ref(v_lhs_3423_);
lean_dec_ref(v_proof_3421_);
return v___x_3813_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3912_ = _args[0];
lean_object* v_isHEq_3913_ = _args[1];
lean_object* v_lhs_3914_ = _args[2];
lean_object* v_rhs_3915_ = _args[3];
lean_object* v_lhsNode_3916_ = _args[4];
lean_object* v_rhsNode_3917_ = _args[5];
lean_object* v_lhsRoot_3918_ = _args[6];
lean_object* v_rhsRoot_3919_ = _args[7];
lean_object* v_flipped_3920_ = _args[8];
lean_object* v_a_3921_ = _args[9];
lean_object* v_a_3922_ = _args[10];
lean_object* v_a_3923_ = _args[11];
lean_object* v_a_3924_ = _args[12];
lean_object* v_a_3925_ = _args[13];
lean_object* v_a_3926_ = _args[14];
lean_object* v_a_3927_ = _args[15];
lean_object* v_a_3928_ = _args[16];
lean_object* v_a_3929_ = _args[17];
lean_object* v_a_3930_ = _args[18];
lean_object* v_a_3931_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3932_; uint8_t v_flipped_boxed_3933_; lean_object* v_res_3934_; 
v_isHEq_boxed_3932_ = lean_unbox(v_isHEq_3913_);
v_flipped_boxed_3933_ = lean_unbox(v_flipped_3920_);
v_res_3934_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3912_, v_isHEq_boxed_3932_, v_lhs_3914_, v_rhs_3915_, v_lhsNode_3916_, v_rhsNode_3917_, v_lhsRoot_3918_, v_rhsRoot_3919_, v_flipped_boxed_3933_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec(v_a_3921_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3935_, lean_object* v_as_x27_3936_, lean_object* v_b_3937_, lean_object* v_a_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3936_, v_b_3937_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3951_, lean_object* v_as_x27_3952_, lean_object* v_b_3953_, lean_object* v_a_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3951_, v_as_x27_3952_, v_b_3953_, v_a_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec(v_as_x27_3952_);
lean_dec(v_as_3951_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3967_, lean_object* v_as_x27_3968_, lean_object* v_b_3969_, lean_object* v_a_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3968_, v_b_3969_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3983_, lean_object* v_as_x27_3984_, lean_object* v_b_3985_, lean_object* v_a_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3983_, v_as_x27_3984_, v_b_3985_, v_a_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec(v_as_x27_3984_);
lean_dec(v_as_3983_);
return v_res_3998_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4001_ = l_Lean_stringToMessageData(v___x_4000_);
return v___x_4001_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4007_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4008_ = l_Lean_Name_append(v___x_4007_, v___x_4006_);
return v___x_4008_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4011_ = l_Lean_stringToMessageData(v___x_4010_);
return v___x_4011_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4014_ = l_Lean_stringToMessageData(v___x_4013_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4015_, lean_object* v_rhs_4016_, lean_object* v_proof_4017_, uint8_t v_isHEq_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4033_ = lean_st_ref_get(v_a_4019_);
lean_inc_ref(v_lhs_4015_);
v___x_4034_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4033_, v_lhs_4015_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
lean_dec(v___x_4033_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
v___x_4036_ = lean_st_ref_get(v_a_4019_);
lean_inc_ref(v_rhs_4016_);
v___x_4037_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4036_, v_rhs_4016_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
lean_dec(v___x_4036_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v_root_4039_; lean_object* v_root_4040_; size_t v___x_4041_; size_t v___x_4042_; uint8_t v___x_4043_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v_root_4039_ = lean_ctor_get(v_a_4035_, 2);
v_root_4040_ = lean_ctor_get(v_a_4038_, 2);
v___x_4041_ = lean_ptr_addr(v_root_4039_);
v___x_4042_ = lean_ptr_addr(v_root_4040_);
v___x_4043_ = lean_usize_dec_eq(v___x_4041_, v___x_4042_);
if (v___x_4043_ == 0)
{
lean_object* v_toCold_4044_; lean_object* v_options_4045_; lean_object* v_inheritedTraceOptions_4046_; uint8_t v_hasTrace_4047_; uint8_t v___x_4048_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4086_; uint8_t v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4114_; uint8_t v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4144_; uint8_t v___y_4145_; lean_object* v___y_4146_; uint8_t v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4160_; lean_object* v___y_4161_; uint8_t v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; uint8_t v___y_4173_; lean_object* v___y_4176_; lean_object* v___y_4177_; uint8_t v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; uint8_t v___y_4189_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v_size_4194_; uint8_t v_interpreted_4195_; uint8_t v_ctor_4196_; uint8_t v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; uint8_t v___y_4208_; lean_object* v___y_4212_; lean_object* v___y_4213_; uint8_t v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; uint8_t v_ctor_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; uint8_t v___y_4226_; lean_object* v___y_4234_; lean_object* v___y_4235_; uint8_t v_valueInconsistency_4236_; uint8_t v_trueEqFalse_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; uint8_t v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; 
v_toCold_4044_ = lean_ctor_get(v_a_4027_, 0);
v_options_4045_ = lean_ctor_get(v_toCold_4044_, 2);
v_inheritedTraceOptions_4046_ = lean_ctor_get(v_toCold_4044_, 11);
v_hasTrace_4047_ = lean_ctor_get_uint8(v_options_4045_, sizeof(void*)*1);
v___x_4048_ = 1;
if (v_hasTrace_4047_ == 0)
{
v___y_4294_ = v_a_4019_;
v___y_4295_ = v_a_4020_;
v___y_4296_ = v_a_4021_;
v___y_4297_ = v_a_4022_;
v___y_4298_ = v_a_4023_;
v___y_4299_ = v_a_4024_;
v___y_4300_ = v_a_4025_;
v___y_4301_ = v_a_4026_;
v___y_4302_ = v_a_4027_;
v___y_4303_ = v_a_4028_;
goto v___jp_4293_;
}
else
{
lean_object* v___x_4337_; lean_object* v_____do__lift_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
v___x_4337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4352_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4353_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4046_, v_options_4045_, v___x_4352_);
if (v___x_4353_ == 0)
{
v___y_4294_ = v_a_4019_;
v___y_4295_ = v_a_4020_;
v___y_4296_ = v_a_4021_;
v___y_4297_ = v_a_4022_;
v___y_4298_ = v_a_4023_;
v___y_4299_ = v_a_4024_;
v___y_4300_ = v_a_4025_;
v___y_4301_ = v_a_4026_;
v___y_4302_ = v_a_4027_;
v___y_4303_ = v_a_4028_;
goto v___jp_4293_;
}
else
{
lean_object* v___x_4354_; 
v___x_4354_ = l_Lean_Meta_Grind_updateLastTag(v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_dec_ref_known(v___x_4354_, 1);
if (v_isHEq_4018_ == 0)
{
lean_object* v___x_4355_; 
lean_inc_ref(v_rhs_4016_);
lean_inc_ref(v_lhs_4015_);
v___x_4355_ = l_Lean_Meta_mkEq(v_lhs_4015_, v_rhs_4016_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v_____do__lift_4339_ = v_a_4356_;
v___y_4340_ = v_a_4019_;
v___y_4341_ = v_a_4020_;
v___y_4342_ = v_a_4021_;
v___y_4343_ = v_a_4022_;
v___y_4344_ = v_a_4023_;
v___y_4345_ = v_a_4024_;
v___y_4346_ = v_a_4025_;
v___y_4347_ = v_a_4026_;
v___y_4348_ = v_a_4027_;
v___y_4349_ = v_a_4028_;
goto v___jp_4338_;
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec(v_a_4038_);
lean_dec(v_a_4035_);
lean_dec_ref(v_proof_4017_);
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
v_a_4357_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4355_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4355_);
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
lean_object* v___x_4365_; 
lean_inc_ref(v_rhs_4016_);
lean_inc_ref(v_lhs_4015_);
v___x_4365_ = l_Lean_Meta_mkHEq(v_lhs_4015_, v_rhs_4016_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_a_4366_);
lean_dec_ref_known(v___x_4365_, 1);
v_____do__lift_4339_ = v_a_4366_;
v___y_4340_ = v_a_4019_;
v___y_4341_ = v_a_4020_;
v___y_4342_ = v_a_4021_;
v___y_4343_ = v_a_4022_;
v___y_4344_ = v_a_4023_;
v___y_4345_ = v_a_4024_;
v___y_4346_ = v_a_4025_;
v___y_4347_ = v_a_4026_;
v___y_4348_ = v_a_4027_;
v___y_4349_ = v_a_4028_;
goto v___jp_4338_;
}
else
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
lean_dec(v_a_4038_);
lean_dec(v_a_4035_);
lean_dec_ref(v_proof_4017_);
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
v_a_4367_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___x_4365_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4365_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
}
else
{
lean_dec(v_a_4038_);
lean_dec(v_a_4035_);
lean_dec_ref(v_proof_4017_);
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
return v___x_4354_;
}
}
v___jp_4338_:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4350_ = l_Lean_MessageData_ofExpr(v_____do__lift_4339_);
v___x_4351_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4337_, v___x_4350_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_dec_ref_known(v___x_4351_, 1);
v___y_4294_ = v___y_4340_;
v___y_4295_ = v___y_4341_;
v___y_4296_ = v___y_4342_;
v___y_4297_ = v___y_4343_;
v___y_4298_ = v___y_4344_;
v___y_4299_ = v___y_4345_;
v___y_4300_ = v___y_4346_;
v___y_4301_ = v___y_4347_;
v___y_4302_ = v___y_4348_;
v___y_4303_ = v___y_4349_;
goto v___jp_4293_;
}
else
{
lean_dec(v_a_4038_);
lean_dec(v_a_4035_);
lean_dec_ref(v_proof_4017_);
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
return v___x_4351_;
}
}
}
v___jp_4049_:
{
lean_object* v_toCold_4060_; lean_object* v_options_4061_; uint8_t v_hasTrace_4062_; 
v_toCold_4060_ = lean_ctor_get(v___y_4058_, 0);
v_options_4061_ = lean_ctor_get(v_toCold_4060_, 2);
v_hasTrace_4062_ = lean_ctor_get_uint8(v_options_4061_, sizeof(void*)*1);
if (v_hasTrace_4062_ == 0)
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_Meta_Grind_checkInvariants(v___x_4043_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v___x_4063_;
}
else
{
lean_object* v_inheritedTraceOptions_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; uint8_t v___x_4067_; 
v_inheritedTraceOptions_4064_ = lean_ctor_get(v_toCold_4060_, 11);
v___x_4065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4066_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4067_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4064_, v_options_4061_, v___x_4066_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Meta_Grind_checkInvariants(v___x_4043_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v___x_4068_;
}
else
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_Meta_Grind_updateLastTag(v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
lean_dec_ref_known(v___x_4069_, 1);
v___x_4070_ = lean_st_ref_get(v___y_4050_);
v___x_4071_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4070_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
lean_dec(v___x_4070_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v___x_4073_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
lean_ctor_set(v___x_4074_, 1, v_a_4072_);
v___x_4075_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4065_, v___x_4074_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v___x_4076_; 
lean_dec_ref_known(v___x_4075_, 1);
v___x_4076_ = l_Lean_Meta_Grind_checkInvariants(v___x_4043_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v___x_4076_;
}
else
{
return v___x_4075_;
}
}
else
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4084_; 
v_a_4077_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4079_ = v___x_4071_;
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4071_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4082_; 
if (v_isShared_4080_ == 0)
{
v___x_4082_ = v___x_4079_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
}
}
else
{
return v___x_4069_;
}
}
}
}
v___jp_4085_:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4089_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; uint8_t v___x_4101_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref_known(v___x_4099_, 1);
v___x_4101_ = lean_unbox(v_a_4100_);
lean_dec(v_a_4100_);
if (v___x_4101_ == 0)
{
if (v___y_4087_ == 0)
{
lean_dec_ref(v___y_4088_);
lean_dec_ref(v___y_4086_);
v___y_4050_ = v___y_4089_;
v___y_4051_ = v___y_4090_;
v___y_4052_ = v___y_4091_;
v___y_4053_ = v___y_4092_;
v___y_4054_ = v___y_4093_;
v___y_4055_ = v___y_4094_;
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
v___y_4059_ = v___y_4098_;
goto v___jp_4049_;
}
else
{
lean_object* v_self_4102_; lean_object* v_self_4103_; lean_object* v___x_4104_; 
v_self_4102_ = lean_ctor_get(v___y_4088_, 0);
lean_inc_ref(v_self_4102_);
lean_dec_ref(v___y_4088_);
v_self_4103_ = lean_ctor_get(v___y_4086_, 0);
lean_inc_ref(v_self_4103_);
lean_dec_ref(v___y_4086_);
v___x_4104_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4102_, v_self_4103_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_dec_ref_known(v___x_4104_, 1);
v___y_4050_ = v___y_4089_;
v___y_4051_ = v___y_4090_;
v___y_4052_ = v___y_4091_;
v___y_4053_ = v___y_4092_;
v___y_4054_ = v___y_4093_;
v___y_4055_ = v___y_4094_;
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
v___y_4059_ = v___y_4098_;
goto v___jp_4049_;
}
else
{
return v___x_4104_;
}
}
}
else
{
lean_dec_ref(v___y_4088_);
lean_dec_ref(v___y_4086_);
v___y_4050_ = v___y_4089_;
v___y_4051_ = v___y_4090_;
v___y_4052_ = v___y_4091_;
v___y_4053_ = v___y_4092_;
v___y_4054_ = v___y_4093_;
v___y_4055_ = v___y_4094_;
v___y_4056_ = v___y_4095_;
v___y_4057_ = v___y_4096_;
v___y_4058_ = v___y_4097_;
v___y_4059_ = v___y_4098_;
goto v___jp_4049_;
}
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec_ref(v___y_4088_);
lean_dec_ref(v___y_4086_);
v_a_4105_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4099_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4099_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
v___jp_4113_:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4117_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; uint8_t v___x_4129_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
v___x_4129_ = lean_unbox(v_a_4128_);
lean_dec(v_a_4128_);
if (v___x_4129_ == 0)
{
uint8_t v_ctor_4130_; 
v_ctor_4130_ = lean_ctor_get_uint8(v___y_4116_, sizeof(void*)*12 + 2);
if (v_ctor_4130_ == 0)
{
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
v___y_4098_ = v___y_4126_;
goto v___jp_4085_;
}
else
{
uint8_t v_ctor_4131_; 
v_ctor_4131_ = lean_ctor_get_uint8(v___y_4114_, sizeof(void*)*12 + 2);
if (v_ctor_4131_ == 0)
{
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
v___y_4098_ = v___y_4126_;
goto v___jp_4085_;
}
else
{
lean_object* v_self_4132_; lean_object* v_self_4133_; lean_object* v___x_4134_; 
v_self_4132_ = lean_ctor_get(v___y_4116_, 0);
v_self_4133_ = lean_ctor_get(v___y_4114_, 0);
lean_inc_ref(v_self_4133_);
lean_inc_ref(v_self_4132_);
v___x_4134_ = l_Lean_Meta_Grind_propagateCtor(v_self_4132_, v_self_4133_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_dec_ref_known(v___x_4134_, 1);
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
v___y_4098_ = v___y_4126_;
goto v___jp_4085_;
}
else
{
lean_dec_ref(v___y_4116_);
lean_dec_ref(v___y_4114_);
return v___x_4134_;
}
}
}
}
else
{
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
v___y_4098_ = v___y_4126_;
goto v___jp_4085_;
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec_ref(v___y_4116_);
lean_dec_ref(v___y_4114_);
v_a_4135_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4127_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4127_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
v___jp_4143_:
{
if (v___y_4147_ == 0)
{
v___y_4114_ = v___y_4144_;
v___y_4115_ = v___y_4145_;
v___y_4116_ = v___y_4146_;
v___y_4117_ = v___y_4148_;
v___y_4118_ = v___y_4149_;
v___y_4119_ = v___y_4150_;
v___y_4120_ = v___y_4151_;
v___y_4121_ = v___y_4152_;
v___y_4122_ = v___y_4153_;
v___y_4123_ = v___y_4154_;
v___y_4124_ = v___y_4155_;
v___y_4125_ = v___y_4156_;
v___y_4126_ = v___y_4157_;
goto v___jp_4113_;
}
else
{
lean_object* v___x_4158_; 
v___x_4158_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_dec_ref_known(v___x_4158_, 1);
v___y_4114_ = v___y_4144_;
v___y_4115_ = v___y_4145_;
v___y_4116_ = v___y_4146_;
v___y_4117_ = v___y_4148_;
v___y_4118_ = v___y_4149_;
v___y_4119_ = v___y_4150_;
v___y_4120_ = v___y_4151_;
v___y_4121_ = v___y_4152_;
v___y_4122_ = v___y_4153_;
v___y_4123_ = v___y_4154_;
v___y_4124_ = v___y_4155_;
v___y_4125_ = v___y_4156_;
v___y_4126_ = v___y_4157_;
goto v___jp_4113_;
}
else
{
lean_dec_ref(v___y_4146_);
lean_dec_ref(v___y_4144_);
return v___x_4158_;
}
}
}
v___jp_4159_:
{
lean_object* v___x_4174_; 
lean_inc_ref(v___y_4164_);
lean_inc_ref(v___y_4161_);
v___x_4174_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4017_, v_isHEq_4018_, v_rhs_4016_, v_lhs_4015_, v_a_4038_, v_a_4035_, v___y_4161_, v___y_4164_, v___x_4048_, v___y_4170_, v___y_4165_, v___y_4171_, v___y_4167_, v___y_4169_, v___y_4160_, v___y_4168_, v___y_4166_, v___y_4163_, v___y_4172_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_dec_ref_known(v___x_4174_, 1);
v___y_4144_ = v___y_4161_;
v___y_4145_ = v___y_4162_;
v___y_4146_ = v___y_4164_;
v___y_4147_ = v___y_4173_;
v___y_4148_ = v___y_4170_;
v___y_4149_ = v___y_4165_;
v___y_4150_ = v___y_4171_;
v___y_4151_ = v___y_4167_;
v___y_4152_ = v___y_4169_;
v___y_4153_ = v___y_4160_;
v___y_4154_ = v___y_4168_;
v___y_4155_ = v___y_4166_;
v___y_4156_ = v___y_4163_;
v___y_4157_ = v___y_4172_;
goto v___jp_4143_;
}
else
{
lean_dec_ref(v___y_4164_);
lean_dec_ref(v___y_4161_);
return v___x_4174_;
}
}
v___jp_4175_:
{
lean_object* v___x_4190_; 
lean_inc_ref(v___y_4177_);
lean_inc_ref(v___y_4180_);
v___x_4190_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4017_, v_isHEq_4018_, v_lhs_4015_, v_rhs_4016_, v_a_4035_, v_a_4038_, v___y_4180_, v___y_4177_, v___x_4043_, v___y_4186_, v___y_4181_, v___y_4187_, v___y_4183_, v___y_4185_, v___y_4176_, v___y_4184_, v___y_4182_, v___y_4179_, v___y_4188_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_dec_ref_known(v___x_4190_, 1);
v___y_4144_ = v___y_4177_;
v___y_4145_ = v___y_4178_;
v___y_4146_ = v___y_4180_;
v___y_4147_ = v___y_4189_;
v___y_4148_ = v___y_4186_;
v___y_4149_ = v___y_4181_;
v___y_4150_ = v___y_4187_;
v___y_4151_ = v___y_4183_;
v___y_4152_ = v___y_4185_;
v___y_4153_ = v___y_4176_;
v___y_4154_ = v___y_4184_;
v___y_4155_ = v___y_4182_;
v___y_4156_ = v___y_4179_;
v___y_4157_ = v___y_4188_;
goto v___jp_4143_;
}
else
{
lean_dec_ref(v___y_4180_);
lean_dec_ref(v___y_4177_);
return v___x_4190_;
}
}
v___jp_4191_:
{
lean_object* v_size_4209_; uint8_t v___x_4210_; 
v_size_4209_ = lean_ctor_get(v___y_4199_, 6);
v___x_4210_ = lean_nat_dec_lt(v_size_4194_, v_size_4209_);
lean_dec(v_size_4194_);
if (v___x_4210_ == 0)
{
v___y_4176_ = v___y_4192_;
v___y_4177_ = v___y_4193_;
v___y_4178_ = v___y_4197_;
v___y_4179_ = v___y_4198_;
v___y_4180_ = v___y_4199_;
v___y_4181_ = v___y_4200_;
v___y_4182_ = v___y_4201_;
v___y_4183_ = v___y_4202_;
v___y_4184_ = v___y_4203_;
v___y_4185_ = v___y_4204_;
v___y_4186_ = v___y_4205_;
v___y_4187_ = v___y_4206_;
v___y_4188_ = v___y_4207_;
v___y_4189_ = v___y_4208_;
goto v___jp_4175_;
}
else
{
if (v_interpreted_4195_ == 0)
{
if (v_ctor_4196_ == 0)
{
v___y_4160_ = v___y_4192_;
v___y_4161_ = v___y_4193_;
v___y_4162_ = v___y_4197_;
v___y_4163_ = v___y_4198_;
v___y_4164_ = v___y_4199_;
v___y_4165_ = v___y_4200_;
v___y_4166_ = v___y_4201_;
v___y_4167_ = v___y_4202_;
v___y_4168_ = v___y_4203_;
v___y_4169_ = v___y_4204_;
v___y_4170_ = v___y_4205_;
v___y_4171_ = v___y_4206_;
v___y_4172_ = v___y_4207_;
v___y_4173_ = v___y_4208_;
goto v___jp_4159_;
}
else
{
v___y_4176_ = v___y_4192_;
v___y_4177_ = v___y_4193_;
v___y_4178_ = v___y_4197_;
v___y_4179_ = v___y_4198_;
v___y_4180_ = v___y_4199_;
v___y_4181_ = v___y_4200_;
v___y_4182_ = v___y_4201_;
v___y_4183_ = v___y_4202_;
v___y_4184_ = v___y_4203_;
v___y_4185_ = v___y_4204_;
v___y_4186_ = v___y_4205_;
v___y_4187_ = v___y_4206_;
v___y_4188_ = v___y_4207_;
v___y_4189_ = v___y_4208_;
goto v___jp_4175_;
}
}
else
{
v___y_4176_ = v___y_4192_;
v___y_4177_ = v___y_4193_;
v___y_4178_ = v___y_4197_;
v___y_4179_ = v___y_4198_;
v___y_4180_ = v___y_4199_;
v___y_4181_ = v___y_4200_;
v___y_4182_ = v___y_4201_;
v___y_4183_ = v___y_4202_;
v___y_4184_ = v___y_4203_;
v___y_4185_ = v___y_4204_;
v___y_4186_ = v___y_4205_;
v___y_4187_ = v___y_4206_;
v___y_4188_ = v___y_4207_;
v___y_4189_ = v___y_4208_;
goto v___jp_4175_;
}
}
}
v___jp_4211_:
{
if (v_ctor_4217_ == 0)
{
lean_object* v_size_4227_; uint8_t v_interpreted_4228_; uint8_t v_ctor_4229_; 
v_size_4227_ = lean_ctor_get(v___y_4213_, 6);
lean_inc(v_size_4227_);
v_interpreted_4228_ = lean_ctor_get_uint8(v___y_4213_, sizeof(void*)*12 + 1);
v_ctor_4229_ = lean_ctor_get_uint8(v___y_4213_, sizeof(void*)*12 + 2);
v___y_4192_ = v___y_4212_;
v___y_4193_ = v___y_4213_;
v_size_4194_ = v_size_4227_;
v_interpreted_4195_ = v_interpreted_4228_;
v_ctor_4196_ = v_ctor_4229_;
v___y_4197_ = v___y_4214_;
v___y_4198_ = v___y_4215_;
v___y_4199_ = v___y_4216_;
v___y_4200_ = v___y_4218_;
v___y_4201_ = v___y_4219_;
v___y_4202_ = v___y_4220_;
v___y_4203_ = v___y_4221_;
v___y_4204_ = v___y_4222_;
v___y_4205_ = v___y_4223_;
v___y_4206_ = v___y_4224_;
v___y_4207_ = v___y_4225_;
v___y_4208_ = v___y_4226_;
goto v___jp_4191_;
}
else
{
uint8_t v_ctor_4230_; 
v_ctor_4230_ = lean_ctor_get_uint8(v___y_4213_, sizeof(void*)*12 + 2);
if (v_ctor_4230_ == 0)
{
v___y_4160_ = v___y_4212_;
v___y_4161_ = v___y_4213_;
v___y_4162_ = v___y_4214_;
v___y_4163_ = v___y_4215_;
v___y_4164_ = v___y_4216_;
v___y_4165_ = v___y_4218_;
v___y_4166_ = v___y_4219_;
v___y_4167_ = v___y_4220_;
v___y_4168_ = v___y_4221_;
v___y_4169_ = v___y_4222_;
v___y_4170_ = v___y_4223_;
v___y_4171_ = v___y_4224_;
v___y_4172_ = v___y_4225_;
v___y_4173_ = v___y_4226_;
goto v___jp_4159_;
}
else
{
lean_object* v_size_4231_; uint8_t v_interpreted_4232_; 
v_size_4231_ = lean_ctor_get(v___y_4213_, 6);
lean_inc(v_size_4231_);
v_interpreted_4232_ = lean_ctor_get_uint8(v___y_4213_, sizeof(void*)*12 + 1);
v___y_4192_ = v___y_4212_;
v___y_4193_ = v___y_4213_;
v_size_4194_ = v_size_4231_;
v_interpreted_4195_ = v_interpreted_4232_;
v_ctor_4196_ = v_ctor_4230_;
v___y_4197_ = v___y_4214_;
v___y_4198_ = v___y_4215_;
v___y_4199_ = v___y_4216_;
v___y_4200_ = v___y_4218_;
v___y_4201_ = v___y_4219_;
v___y_4202_ = v___y_4220_;
v___y_4203_ = v___y_4221_;
v___y_4204_ = v___y_4222_;
v___y_4205_ = v___y_4223_;
v___y_4206_ = v___y_4224_;
v___y_4207_ = v___y_4225_;
v___y_4208_ = v___y_4226_;
goto v___jp_4191_;
}
}
}
v___jp_4233_:
{
uint8_t v_interpreted_4248_; 
v_interpreted_4248_ = lean_ctor_get_uint8(v___y_4235_, sizeof(void*)*12 + 1);
if (v_interpreted_4248_ == 0)
{
uint8_t v_ctor_4249_; 
v_ctor_4249_ = lean_ctor_get_uint8(v___y_4235_, sizeof(void*)*12 + 2);
v___y_4212_ = v___y_4243_;
v___y_4213_ = v___y_4234_;
v___y_4214_ = v_valueInconsistency_4236_;
v___y_4215_ = v___y_4246_;
v___y_4216_ = v___y_4235_;
v_ctor_4217_ = v_ctor_4249_;
v___y_4218_ = v___y_4239_;
v___y_4219_ = v___y_4245_;
v___y_4220_ = v___y_4241_;
v___y_4221_ = v___y_4244_;
v___y_4222_ = v___y_4242_;
v___y_4223_ = v___y_4238_;
v___y_4224_ = v___y_4240_;
v___y_4225_ = v___y_4247_;
v___y_4226_ = v_trueEqFalse_4237_;
goto v___jp_4211_;
}
else
{
uint8_t v_interpreted_4250_; 
v_interpreted_4250_ = lean_ctor_get_uint8(v___y_4234_, sizeof(void*)*12 + 1);
if (v_interpreted_4250_ == 0)
{
v___y_4160_ = v___y_4243_;
v___y_4161_ = v___y_4234_;
v___y_4162_ = v_valueInconsistency_4236_;
v___y_4163_ = v___y_4246_;
v___y_4164_ = v___y_4235_;
v___y_4165_ = v___y_4239_;
v___y_4166_ = v___y_4245_;
v___y_4167_ = v___y_4241_;
v___y_4168_ = v___y_4244_;
v___y_4169_ = v___y_4242_;
v___y_4170_ = v___y_4238_;
v___y_4171_ = v___y_4240_;
v___y_4172_ = v___y_4247_;
v___y_4173_ = v_trueEqFalse_4237_;
goto v___jp_4159_;
}
else
{
uint8_t v_ctor_4251_; 
v_ctor_4251_ = lean_ctor_get_uint8(v___y_4235_, sizeof(void*)*12 + 2);
v___y_4212_ = v___y_4243_;
v___y_4213_ = v___y_4234_;
v___y_4214_ = v_valueInconsistency_4236_;
v___y_4215_ = v___y_4246_;
v___y_4216_ = v___y_4235_;
v_ctor_4217_ = v_ctor_4251_;
v___y_4218_ = v___y_4239_;
v___y_4219_ = v___y_4245_;
v___y_4220_ = v___y_4241_;
v___y_4221_ = v___y_4244_;
v___y_4222_ = v___y_4242_;
v___y_4223_ = v___y_4238_;
v___y_4224_ = v___y_4240_;
v___y_4225_ = v___y_4247_;
v___y_4226_ = v_trueEqFalse_4237_;
goto v___jp_4211_;
}
}
}
v___jp_4252_:
{
lean_object* v___x_4265_; 
v___x_4265_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4257_, v___y_4262_, v___y_4260_, v___y_4258_, v___y_4263_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_dec_ref_known(v___x_4265_, 1);
v___y_4234_ = v___y_4255_;
v___y_4235_ = v___y_4256_;
v_valueInconsistency_4236_ = v___x_4043_;
v_trueEqFalse_4237_ = v___x_4048_;
v___y_4238_ = v___y_4257_;
v___y_4239_ = v___y_4254_;
v___y_4240_ = v___y_4253_;
v___y_4241_ = v___y_4264_;
v___y_4242_ = v___y_4261_;
v___y_4243_ = v___y_4259_;
v___y_4244_ = v___y_4262_;
v___y_4245_ = v___y_4260_;
v___y_4246_ = v___y_4258_;
v___y_4247_ = v___y_4263_;
goto v___jp_4233_;
}
else
{
lean_dec_ref(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v_a_4038_);
lean_dec(v_a_4035_);
lean_dec_ref(v_proof_4017_);
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
return v___x_4265_;
}
}
v___jp_4266_:
{
if (v___y_4276_ == 0)
{
lean_object* v___x_4282_; 
v___x_4282_ = l_Lean_Meta_Grind_hasSameType(v___y_4280_, v___y_4281_, v___y_4277_, v___y_4274_, v___y_4272_, v___y_4278_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; uint8_t v___x_4284_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4282_, 1);
v___x_4284_ = lean_unbox(v_a_4283_);
lean_dec(v_a_4283_);
if (v___x_4284_ == 0)
{
v___y_4234_ = v___y_4269_;
v___y_4235_ = v___y_4270_;
v_valueInconsistency_4236_ = v___x_4043_;
v_trueEqFalse_4237_ = v___x_4043_;
v___y_4238_ = v___y_4273_;
v___y_4239_ = v___y_4268_;
v___y_4240_ = v___y_4267_;
v___y_4241_ = v___y_4279_;
v___y_4242_ = v___y_4275_;
v___y_4243_ = v___y_4271_;
v___y_4244_ = v___y_4277_;
v___y_4245_ = v___y_4274_;
v___y_4246_ = v___y_4272_;
v___y_4247_ = v___y_4278_;
goto v___jp_4233_;
}
else
{
v___y_4234_ = v___y_4269_;
v___y_4235_ = v___y_4270_;
v_valueInconsistency_4236_ = v___x_4048_;
v_trueEqFalse_4237_ = v___x_4043_;
v___y_4238_ = v___y_4273_;
v___y_4239_ = v___y_4268_;
v___y_4240_ = v___y_4267_;
v___y_4241_ = v___y_4279_;
v___y_4242_ = v___y_4275_;
v___y_4243_ = v___y_4271_;
v___y_4244_ = v___y_4277_;
v___y_4245_ = v___y_4274_;
v___y_4246_ = v___y_4272_;
v___y_4247_ = v___y_4278_;
goto v___jp_4233_;
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_dec_ref(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v_a_4038_);
lean_dec(v_a_4035_);
lean_dec_ref(v_proof_4017_);
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
v_a_4285_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4282_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4282_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
else
{
lean_dec_ref(v___y_4281_);
lean_dec_ref(v___y_4280_);
v___y_4234_ = v___y_4269_;
v___y_4235_ = v___y_4270_;
v_valueInconsistency_4236_ = v___x_4048_;
v_trueEqFalse_4237_ = v___x_4043_;
v___y_4238_ = v___y_4273_;
v___y_4239_ = v___y_4268_;
v___y_4240_ = v___y_4267_;
v___y_4241_ = v___y_4279_;
v___y_4242_ = v___y_4275_;
v___y_4243_ = v___y_4271_;
v___y_4244_ = v___y_4277_;
v___y_4245_ = v___y_4274_;
v___y_4246_ = v___y_4272_;
v___y_4247_ = v___y_4278_;
goto v___jp_4233_;
}
}
v___jp_4293_:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = lean_st_ref_get(v___y_4294_);
lean_inc_ref(v_root_4039_);
v___x_4305_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4304_, v_root_4039_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___x_4304_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___x_4305_, 1);
v___x_4307_ = lean_st_ref_get(v___y_4294_);
lean_inc_ref(v_root_4040_);
v___x_4308_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4307_, v_root_4040_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___x_4307_);
if (lean_obj_tag(v___x_4308_) == 0)
{
uint8_t v_interpreted_4309_; 
v_interpreted_4309_ = lean_ctor_get_uint8(v_a_4306_, sizeof(void*)*12 + 1);
if (v_interpreted_4309_ == 0)
{
lean_object* v_a_4310_; uint8_t v_ctor_4311_; 
v_a_4310_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4308_, 1);
v_ctor_4311_ = lean_ctor_get_uint8(v_a_4306_, sizeof(void*)*12 + 2);
v___y_4212_ = v___y_4299_;
v___y_4213_ = v_a_4310_;
v___y_4214_ = v___x_4043_;
v___y_4215_ = v___y_4302_;
v___y_4216_ = v_a_4306_;
v_ctor_4217_ = v_ctor_4311_;
v___y_4218_ = v___y_4295_;
v___y_4219_ = v___y_4301_;
v___y_4220_ = v___y_4297_;
v___y_4221_ = v___y_4300_;
v___y_4222_ = v___y_4298_;
v___y_4223_ = v___y_4294_;
v___y_4224_ = v___y_4296_;
v___y_4225_ = v___y_4303_;
v___y_4226_ = v___x_4043_;
goto v___jp_4211_;
}
else
{
lean_object* v_a_4312_; uint8_t v_interpreted_4313_; 
v_a_4312_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4308_, 1);
v_interpreted_4313_ = lean_ctor_get_uint8(v_a_4312_, sizeof(void*)*12 + 1);
if (v_interpreted_4313_ == 0)
{
v___y_4160_ = v___y_4299_;
v___y_4161_ = v_a_4312_;
v___y_4162_ = v___x_4043_;
v___y_4163_ = v___y_4302_;
v___y_4164_ = v_a_4306_;
v___y_4165_ = v___y_4295_;
v___y_4166_ = v___y_4301_;
v___y_4167_ = v___y_4297_;
v___y_4168_ = v___y_4300_;
v___y_4169_ = v___y_4298_;
v___y_4170_ = v___y_4294_;
v___y_4171_ = v___y_4296_;
v___y_4172_ = v___y_4303_;
v___y_4173_ = v___x_4043_;
goto v___jp_4159_;
}
else
{
lean_object* v_self_4314_; uint8_t v_ctor_4315_; uint8_t v_heqProofs_4316_; lean_object* v_self_4317_; uint8_t v_heqProofs_4318_; uint8_t v___x_4319_; 
v_self_4314_ = lean_ctor_get(v_a_4306_, 0);
v_ctor_4315_ = lean_ctor_get_uint8(v_a_4306_, sizeof(void*)*12 + 2);
v_heqProofs_4316_ = lean_ctor_get_uint8(v_a_4306_, sizeof(void*)*12 + 4);
v_self_4317_ = lean_ctor_get(v_a_4312_, 0);
v_heqProofs_4318_ = lean_ctor_get_uint8(v_a_4312_, sizeof(void*)*12 + 4);
lean_inc_ref(v_root_4039_);
v___x_4319_ = l_Lean_Expr_isTrue(v_root_4039_);
if (v___x_4319_ == 0)
{
uint8_t v___x_4320_; 
lean_inc_ref(v_root_4040_);
v___x_4320_ = l_Lean_Expr_isTrue(v_root_4040_);
if (v___x_4320_ == 0)
{
if (v_isHEq_4018_ == 0)
{
if (v_heqProofs_4316_ == 0)
{
if (v_heqProofs_4318_ == 0)
{
v___y_4212_ = v___y_4299_;
v___y_4213_ = v_a_4312_;
v___y_4214_ = v___x_4048_;
v___y_4215_ = v___y_4302_;
v___y_4216_ = v_a_4306_;
v_ctor_4217_ = v_ctor_4315_;
v___y_4218_ = v___y_4295_;
v___y_4219_ = v___y_4301_;
v___y_4220_ = v___y_4297_;
v___y_4221_ = v___y_4300_;
v___y_4222_ = v___y_4298_;
v___y_4223_ = v___y_4294_;
v___y_4224_ = v___y_4296_;
v___y_4225_ = v___y_4303_;
v___y_4226_ = v___x_4043_;
goto v___jp_4211_;
}
else
{
lean_inc_ref(v_self_4317_);
lean_inc_ref(v_self_4314_);
v___y_4267_ = v___y_4296_;
v___y_4268_ = v___y_4295_;
v___y_4269_ = v_a_4312_;
v___y_4270_ = v_a_4306_;
v___y_4271_ = v___y_4299_;
v___y_4272_ = v___y_4302_;
v___y_4273_ = v___y_4294_;
v___y_4274_ = v___y_4301_;
v___y_4275_ = v___y_4298_;
v___y_4276_ = v___x_4320_;
v___y_4277_ = v___y_4300_;
v___y_4278_ = v___y_4303_;
v___y_4279_ = v___y_4297_;
v___y_4280_ = v_self_4314_;
v___y_4281_ = v_self_4317_;
goto v___jp_4266_;
}
}
else
{
lean_inc_ref(v_self_4317_);
lean_inc_ref(v_self_4314_);
v___y_4267_ = v___y_4296_;
v___y_4268_ = v___y_4295_;
v___y_4269_ = v_a_4312_;
v___y_4270_ = v_a_4306_;
v___y_4271_ = v___y_4299_;
v___y_4272_ = v___y_4302_;
v___y_4273_ = v___y_4294_;
v___y_4274_ = v___y_4301_;
v___y_4275_ = v___y_4298_;
v___y_4276_ = v___x_4320_;
v___y_4277_ = v___y_4300_;
v___y_4278_ = v___y_4303_;
v___y_4279_ = v___y_4297_;
v___y_4280_ = v_self_4314_;
v___y_4281_ = v_self_4317_;
goto v___jp_4266_;
}
}
else
{
lean_inc_ref(v_self_4317_);
lean_inc_ref(v_self_4314_);
v___y_4267_ = v___y_4296_;
v___y_4268_ = v___y_4295_;
v___y_4269_ = v_a_4312_;
v___y_4270_ = v_a_4306_;
v___y_4271_ = v___y_4299_;
v___y_4272_ = v___y_4302_;
v___y_4273_ = v___y_4294_;
v___y_4274_ = v___y_4301_;
v___y_4275_ = v___y_4298_;
v___y_4276_ = v___x_4320_;
v___y_4277_ = v___y_4300_;
v___y_4278_ = v___y_4303_;
v___y_4279_ = v___y_4297_;
v___y_4280_ = v_self_4314_;
v___y_4281_ = v_self_4317_;
goto v___jp_4266_;
}
}
else
{
v___y_4253_ = v___y_4296_;
v___y_4254_ = v___y_4295_;
v___y_4255_ = v_a_4312_;
v___y_4256_ = v_a_4306_;
v___y_4257_ = v___y_4294_;
v___y_4258_ = v___y_4302_;
v___y_4259_ = v___y_4299_;
v___y_4260_ = v___y_4301_;
v___y_4261_ = v___y_4298_;
v___y_4262_ = v___y_4300_;
v___y_4263_ = v___y_4303_;
v___y_4264_ = v___y_4297_;
goto v___jp_4252_;
}
}
else
{
v___y_4253_ = v___y_4296_;
v___y_4254_ = v___y_4295_;
v___y_4255_ = v_a_4312_;
v___y_4256_ = v_a_4306_;
v___y_4257_ = v___y_4294_;
v___y_4258_ = v___y_4302_;
v___y_4259_ = v___y_4299_;
v___y_4260_ = v___y_4301_;
v___y_4261_ = v___y_4298_;
v___y_4262_ = v___y_4300_;
v___y_4263_ = v___y_4303_;
v___y_4264_ = v___y_4297_;
goto v___jp_4252_;
}
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec(v_a_4306_);
lean_dec(v_a_4038_);
lean_dec(v_a_4035_);
lean_dec_ref(v_proof_4017_);
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
v_a_4321_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4308_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4308_);
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
lean_dec(v_a_4038_);
lean_dec(v_a_4035_);
lean_dec_ref(v_proof_4017_);
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
v_a_4329_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4305_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4305_);
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
}
else
{
lean_object* v_toCold_4375_; lean_object* v_options_4376_; uint8_t v_hasTrace_4377_; 
lean_dec(v_a_4038_);
lean_dec(v_a_4035_);
lean_dec_ref(v_proof_4017_);
v_toCold_4375_ = lean_ctor_get(v_a_4027_, 0);
v_options_4376_ = lean_ctor_get(v_toCold_4375_, 2);
v_hasTrace_4377_ = lean_ctor_get_uint8(v_options_4376_, sizeof(void*)*1);
if (v_hasTrace_4377_ == 0)
{
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
goto v___jp_4030_;
}
else
{
lean_object* v_inheritedTraceOptions_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; uint8_t v___x_4381_; 
v_inheritedTraceOptions_4378_ = lean_ctor_get(v_toCold_4375_, 11);
v___x_4379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4380_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4381_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4378_, v_options_4376_, v___x_4380_);
if (v___x_4381_ == 0)
{
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
goto v___jp_4030_;
}
else
{
lean_object* v___x_4382_; 
v___x_4382_ = l_Lean_Meta_Grind_updateLastTag(v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v___x_4383_; 
lean_dec_ref_known(v___x_4382_, 1);
v___x_4383_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4015_, v_a_4019_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4385_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc(v_a_4384_);
lean_dec_ref_known(v___x_4383_, 1);
v___x_4385_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4016_, v_a_4019_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v___x_4385_, 1);
v___x_4387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4388_, 0, v_a_4384_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
v___x_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
lean_ctor_set(v___x_4389_, 1, v_a_4386_);
v___x_4390_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4379_, v___x_4391_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_dec_ref_known(v___x_4392_, 1);
goto v___jp_4030_;
}
else
{
return v___x_4392_;
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_dec(v_a_4384_);
v_a_4393_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4385_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4385_);
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
lean_dec_ref(v_rhs_4016_);
v_a_4401_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4383_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4383_);
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
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
return v___x_4382_;
}
}
}
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec(v_a_4035_);
lean_dec_ref(v_proof_4017_);
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
v_a_4409_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4037_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4037_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
lean_dec_ref(v_proof_4017_);
lean_dec_ref(v_rhs_4016_);
lean_dec_ref(v_lhs_4015_);
v_a_4417_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4034_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4034_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
v___jp_4030_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = lean_box(0);
v___x_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
return v___x_4032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4425_, lean_object* v_rhs_4426_, lean_object* v_proof_4427_, lean_object* v_isHEq_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_){
_start:
{
uint8_t v_isHEq_boxed_4440_; lean_object* v_res_4441_; 
v_isHEq_boxed_4440_ = lean_unbox(v_isHEq_4428_);
v_res_4441_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4425_, v_rhs_4426_, v_proof_4427_, v_isHEq_boxed_4440_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_);
lean_dec(v_a_4438_);
lean_dec_ref(v_a_4437_);
lean_dec(v_a_4436_);
lean_dec_ref(v_a_4435_);
lean_dec(v_a_4434_);
lean_dec_ref(v_a_4433_);
lean_dec(v_a_4432_);
lean_dec_ref(v_a_4431_);
lean_dec(v_a_4430_);
lean_dec(v_a_4429_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4444_){
_start:
{
lean_object* v___x_4446_; lean_object* v_toGoalState_4447_; lean_object* v_mvarId_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4484_; 
v___x_4446_ = lean_st_ref_take(v_a_4444_);
v_toGoalState_4447_ = lean_ctor_get(v___x_4446_, 0);
v_mvarId_4448_ = lean_ctor_get(v___x_4446_, 1);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4450_ = v___x_4446_;
v_isShared_4451_ = v_isSharedCheck_4484_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_mvarId_4448_);
lean_inc(v_toGoalState_4447_);
lean_dec(v___x_4446_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4484_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v_nextDeclIdx_4452_; lean_object* v_enodeMap_4453_; lean_object* v_exprs_4454_; lean_object* v_parents_4455_; lean_object* v_congrTable_4456_; lean_object* v_appMap_4457_; lean_object* v_indicesFound_4458_; uint8_t v_inconsistent_4459_; lean_object* v_nextIdx_4460_; lean_object* v_newRawFacts_4461_; lean_object* v_facts_4462_; lean_object* v_extThms_4463_; lean_object* v_ematch_4464_; lean_object* v_inj_4465_; lean_object* v_split_4466_; lean_object* v_clean_4467_; lean_object* v_sstates_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4482_; 
v_nextDeclIdx_4452_ = lean_ctor_get(v_toGoalState_4447_, 0);
v_enodeMap_4453_ = lean_ctor_get(v_toGoalState_4447_, 1);
v_exprs_4454_ = lean_ctor_get(v_toGoalState_4447_, 2);
v_parents_4455_ = lean_ctor_get(v_toGoalState_4447_, 3);
v_congrTable_4456_ = lean_ctor_get(v_toGoalState_4447_, 4);
v_appMap_4457_ = lean_ctor_get(v_toGoalState_4447_, 5);
v_indicesFound_4458_ = lean_ctor_get(v_toGoalState_4447_, 6);
v_inconsistent_4459_ = lean_ctor_get_uint8(v_toGoalState_4447_, sizeof(void*)*17);
v_nextIdx_4460_ = lean_ctor_get(v_toGoalState_4447_, 8);
v_newRawFacts_4461_ = lean_ctor_get(v_toGoalState_4447_, 9);
v_facts_4462_ = lean_ctor_get(v_toGoalState_4447_, 10);
v_extThms_4463_ = lean_ctor_get(v_toGoalState_4447_, 11);
v_ematch_4464_ = lean_ctor_get(v_toGoalState_4447_, 12);
v_inj_4465_ = lean_ctor_get(v_toGoalState_4447_, 13);
v_split_4466_ = lean_ctor_get(v_toGoalState_4447_, 14);
v_clean_4467_ = lean_ctor_get(v_toGoalState_4447_, 15);
v_sstates_4468_ = lean_ctor_get(v_toGoalState_4447_, 16);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_toGoalState_4447_);
if (v_isSharedCheck_4482_ == 0)
{
lean_object* v_unused_4483_; 
v_unused_4483_ = lean_ctor_get(v_toGoalState_4447_, 7);
lean_dec(v_unused_4483_);
v___x_4470_ = v_toGoalState_4447_;
v_isShared_4471_ = v_isSharedCheck_4482_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_sstates_4468_);
lean_inc(v_clean_4467_);
lean_inc(v_split_4466_);
lean_inc(v_inj_4465_);
lean_inc(v_ematch_4464_);
lean_inc(v_extThms_4463_);
lean_inc(v_facts_4462_);
lean_inc(v_newRawFacts_4461_);
lean_inc(v_nextIdx_4460_);
lean_inc(v_indicesFound_4458_);
lean_inc(v_appMap_4457_);
lean_inc(v_congrTable_4456_);
lean_inc(v_parents_4455_);
lean_inc(v_exprs_4454_);
lean_inc(v_enodeMap_4453_);
lean_inc(v_nextDeclIdx_4452_);
lean_dec(v_toGoalState_4447_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4482_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4472_ = lean_box(0);
v___x_4473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 7, v___x_4473_);
v___x_4475_ = v___x_4470_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_nextDeclIdx_4452_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_enodeMap_4453_);
lean_ctor_set(v_reuseFailAlloc_4481_, 2, v_exprs_4454_);
lean_ctor_set(v_reuseFailAlloc_4481_, 3, v_parents_4455_);
lean_ctor_set(v_reuseFailAlloc_4481_, 4, v_congrTable_4456_);
lean_ctor_set(v_reuseFailAlloc_4481_, 5, v_appMap_4457_);
lean_ctor_set(v_reuseFailAlloc_4481_, 6, v_indicesFound_4458_);
lean_ctor_set(v_reuseFailAlloc_4481_, 7, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4481_, 8, v_nextIdx_4460_);
lean_ctor_set(v_reuseFailAlloc_4481_, 9, v_newRawFacts_4461_);
lean_ctor_set(v_reuseFailAlloc_4481_, 10, v_facts_4462_);
lean_ctor_set(v_reuseFailAlloc_4481_, 11, v_extThms_4463_);
lean_ctor_set(v_reuseFailAlloc_4481_, 12, v_ematch_4464_);
lean_ctor_set(v_reuseFailAlloc_4481_, 13, v_inj_4465_);
lean_ctor_set(v_reuseFailAlloc_4481_, 14, v_split_4466_);
lean_ctor_set(v_reuseFailAlloc_4481_, 15, v_clean_4467_);
lean_ctor_set(v_reuseFailAlloc_4481_, 16, v_sstates_4468_);
lean_ctor_set_uint8(v_reuseFailAlloc_4481_, sizeof(void*)*17, v_inconsistent_4459_);
v___x_4475_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4477_; 
if (v_isShared_4451_ == 0)
{
lean_ctor_set(v___x_4450_, 0, v___x_4475_);
v___x_4477_ = v___x_4450_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_mvarId_4448_);
v___x_4477_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; 
v___x_4478_ = lean_st_ref_put(v_a_4444_, v___x_4477_);
v___x_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4472_);
return v___x_4479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4485_, lean_object* v_a_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4485_);
lean_dec(v_a_4485_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_){
_start:
{
lean_object* v___x_4499_; 
v___x_4499_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4488_);
return v___x_4499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
lean_dec(v_a_4501_);
lean_dec(v_a_4500_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4512_){
_start:
{
lean_object* v___x_4514_; lean_object* v_toGoalState_4515_; lean_object* v_newFacts_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4514_ = lean_st_ref_get(v_a_4512_);
v_toGoalState_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc_ref(v_toGoalState_4515_);
lean_dec(v___x_4514_);
v_newFacts_4516_ = lean_ctor_get(v_toGoalState_4515_, 7);
lean_inc_ref(v_newFacts_4516_);
lean_dec_ref(v_toGoalState_4515_);
v___x_4517_ = lean_array_get_size(v_newFacts_4516_);
v___x_4518_ = lean_unsigned_to_nat(1u);
v___x_4519_ = lean_nat_sub(v___x_4517_, v___x_4518_);
v___x_4520_ = lean_nat_dec_lt(v___x_4519_, v___x_4517_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
lean_dec(v___x_4519_);
lean_dec_ref(v_newFacts_4516_);
v___x_4521_ = lean_box(0);
v___x_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
return v___x_4522_;
}
else
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v_toGoalState_4526_; lean_object* v_mvarId_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4562_; 
v___x_4523_ = lean_array_fget(v_newFacts_4516_, v___x_4519_);
lean_dec(v___x_4519_);
lean_dec_ref(v_newFacts_4516_);
v___x_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
v___x_4525_ = lean_st_ref_take(v_a_4512_);
v_toGoalState_4526_ = lean_ctor_get(v___x_4525_, 0);
v_mvarId_4527_ = lean_ctor_get(v___x_4525_, 1);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4529_ = v___x_4525_;
v_isShared_4530_ = v_isSharedCheck_4562_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_mvarId_4527_);
lean_inc(v_toGoalState_4526_);
lean_dec(v___x_4525_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4562_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v_nextDeclIdx_4531_; lean_object* v_enodeMap_4532_; lean_object* v_exprs_4533_; lean_object* v_parents_4534_; lean_object* v_congrTable_4535_; lean_object* v_appMap_4536_; lean_object* v_indicesFound_4537_; lean_object* v_newFacts_4538_; uint8_t v_inconsistent_4539_; lean_object* v_nextIdx_4540_; lean_object* v_newRawFacts_4541_; lean_object* v_facts_4542_; lean_object* v_extThms_4543_; lean_object* v_ematch_4544_; lean_object* v_inj_4545_; lean_object* v_split_4546_; lean_object* v_clean_4547_; lean_object* v_sstates_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4561_; 
v_nextDeclIdx_4531_ = lean_ctor_get(v_toGoalState_4526_, 0);
v_enodeMap_4532_ = lean_ctor_get(v_toGoalState_4526_, 1);
v_exprs_4533_ = lean_ctor_get(v_toGoalState_4526_, 2);
v_parents_4534_ = lean_ctor_get(v_toGoalState_4526_, 3);
v_congrTable_4535_ = lean_ctor_get(v_toGoalState_4526_, 4);
v_appMap_4536_ = lean_ctor_get(v_toGoalState_4526_, 5);
v_indicesFound_4537_ = lean_ctor_get(v_toGoalState_4526_, 6);
v_newFacts_4538_ = lean_ctor_get(v_toGoalState_4526_, 7);
v_inconsistent_4539_ = lean_ctor_get_uint8(v_toGoalState_4526_, sizeof(void*)*17);
v_nextIdx_4540_ = lean_ctor_get(v_toGoalState_4526_, 8);
v_newRawFacts_4541_ = lean_ctor_get(v_toGoalState_4526_, 9);
v_facts_4542_ = lean_ctor_get(v_toGoalState_4526_, 10);
v_extThms_4543_ = lean_ctor_get(v_toGoalState_4526_, 11);
v_ematch_4544_ = lean_ctor_get(v_toGoalState_4526_, 12);
v_inj_4545_ = lean_ctor_get(v_toGoalState_4526_, 13);
v_split_4546_ = lean_ctor_get(v_toGoalState_4526_, 14);
v_clean_4547_ = lean_ctor_get(v_toGoalState_4526_, 15);
v_sstates_4548_ = lean_ctor_get(v_toGoalState_4526_, 16);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_toGoalState_4526_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4550_ = v_toGoalState_4526_;
v_isShared_4551_ = v_isSharedCheck_4561_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_sstates_4548_);
lean_inc(v_clean_4547_);
lean_inc(v_split_4546_);
lean_inc(v_inj_4545_);
lean_inc(v_ematch_4544_);
lean_inc(v_extThms_4543_);
lean_inc(v_facts_4542_);
lean_inc(v_newRawFacts_4541_);
lean_inc(v_nextIdx_4540_);
lean_inc(v_newFacts_4538_);
lean_inc(v_indicesFound_4537_);
lean_inc(v_appMap_4536_);
lean_inc(v_congrTable_4535_);
lean_inc(v_parents_4534_);
lean_inc(v_exprs_4533_);
lean_inc(v_enodeMap_4532_);
lean_inc(v_nextDeclIdx_4531_);
lean_dec(v_toGoalState_4526_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4561_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4552_; lean_object* v___x_4554_; 
v___x_4552_ = lean_array_pop(v_newFacts_4538_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 7, v___x_4552_);
v___x_4554_ = v___x_4550_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_nextDeclIdx_4531_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v_enodeMap_4532_);
lean_ctor_set(v_reuseFailAlloc_4560_, 2, v_exprs_4533_);
lean_ctor_set(v_reuseFailAlloc_4560_, 3, v_parents_4534_);
lean_ctor_set(v_reuseFailAlloc_4560_, 4, v_congrTable_4535_);
lean_ctor_set(v_reuseFailAlloc_4560_, 5, v_appMap_4536_);
lean_ctor_set(v_reuseFailAlloc_4560_, 6, v_indicesFound_4537_);
lean_ctor_set(v_reuseFailAlloc_4560_, 7, v___x_4552_);
lean_ctor_set(v_reuseFailAlloc_4560_, 8, v_nextIdx_4540_);
lean_ctor_set(v_reuseFailAlloc_4560_, 9, v_newRawFacts_4541_);
lean_ctor_set(v_reuseFailAlloc_4560_, 10, v_facts_4542_);
lean_ctor_set(v_reuseFailAlloc_4560_, 11, v_extThms_4543_);
lean_ctor_set(v_reuseFailAlloc_4560_, 12, v_ematch_4544_);
lean_ctor_set(v_reuseFailAlloc_4560_, 13, v_inj_4545_);
lean_ctor_set(v_reuseFailAlloc_4560_, 14, v_split_4546_);
lean_ctor_set(v_reuseFailAlloc_4560_, 15, v_clean_4547_);
lean_ctor_set(v_reuseFailAlloc_4560_, 16, v_sstates_4548_);
lean_ctor_set_uint8(v_reuseFailAlloc_4560_, sizeof(void*)*17, v_inconsistent_4539_);
v___x_4554_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
lean_object* v___x_4556_; 
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v___x_4554_);
v___x_4556_ = v___x_4529_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4554_);
lean_ctor_set(v_reuseFailAlloc_4559_, 1, v_mvarId_4527_);
v___x_4556_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; 
v___x_4557_ = lean_st_ref_put(v_a_4512_, v___x_4556_);
v___x_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4524_);
return v___x_4558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4563_, lean_object* v_a_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4563_);
lean_dec(v_a_4563_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_){
_start:
{
lean_object* v___x_4577_; 
v___x_4577_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4566_);
return v___x_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_);
lean_dec(v_a_4587_);
lean_dec_ref(v_a_4586_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
lean_dec(v_a_4583_);
lean_dec_ref(v_a_4582_);
lean_dec(v_a_4581_);
lean_dec_ref(v_a_4580_);
lean_dec(v_a_4579_);
lean_dec(v_a_4578_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4590_, lean_object* v_rhs_4591_, lean_object* v_proof_4592_, uint8_t v_isHEq_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4590_, v_rhs_4591_, v_proof_4592_, v_isHEq_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v___x_4606_; 
lean_dec_ref_known(v___x_4605_, 1);
lean_inc(v_a_4603_);
lean_inc_ref(v_a_4602_);
lean_inc(v_a_4601_);
lean_inc_ref(v_a_4600_);
lean_inc(v_a_4599_);
lean_inc_ref(v_a_4598_);
lean_inc(v_a_4597_);
lean_inc_ref(v_a_4596_);
lean_inc(v_a_4595_);
lean_inc(v_a_4594_);
v___x_4606_ = lean_grind_process_new_facts(v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
return v___x_4606_;
}
else
{
return v___x_4605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4607_, lean_object* v_rhs_4608_, lean_object* v_proof_4609_, lean_object* v_isHEq_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
uint8_t v_isHEq_boxed_4622_; lean_object* v_res_4623_; 
v_isHEq_boxed_4622_ = lean_unbox(v_isHEq_4610_);
v_res_4623_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4607_, v_rhs_4608_, v_proof_4609_, v_isHEq_boxed_4622_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_);
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
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4624_, lean_object* v_rhs_4625_, lean_object* v_proof_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
uint8_t v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = 0;
v___x_4639_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4624_, v_rhs_4625_, v_proof_4626_, v___x_4638_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4640_, lean_object* v_rhs_4641_, lean_object* v_proof_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4640_, v_rhs_4641_, v_proof_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_);
lean_dec(v_a_4652_);
lean_dec_ref(v_a_4651_);
lean_dec(v_a_4650_);
lean_dec_ref(v_a_4649_);
lean_dec(v_a_4648_);
lean_dec_ref(v_a_4647_);
lean_dec(v_a_4646_);
lean_dec_ref(v_a_4645_);
lean_dec(v_a_4644_);
lean_dec(v_a_4643_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4655_, lean_object* v_rhs_4656_, lean_object* v_proof_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
uint8_t v___x_4669_; lean_object* v___x_4670_; 
v___x_4669_ = 1;
v___x_4670_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4655_, v_rhs_4656_, v_proof_4657_, v___x_4669_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4671_, lean_object* v_rhs_4672_, lean_object* v_proof_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4671_, v_rhs_4672_, v_proof_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4686_, lean_object* v_a_4687_){
_start:
{
lean_object* v___x_4689_; lean_object* v_toGoalState_4690_; lean_object* v_mvarId_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4727_; 
v___x_4689_ = lean_st_ref_take(v_a_4687_);
v_toGoalState_4690_ = lean_ctor_get(v___x_4689_, 0);
v_mvarId_4691_ = lean_ctor_get(v___x_4689_, 1);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4693_ = v___x_4689_;
v_isShared_4694_ = v_isSharedCheck_4727_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_mvarId_4691_);
lean_inc(v_toGoalState_4690_);
lean_dec(v___x_4689_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4727_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v_nextDeclIdx_4695_; lean_object* v_enodeMap_4696_; lean_object* v_exprs_4697_; lean_object* v_parents_4698_; lean_object* v_congrTable_4699_; lean_object* v_appMap_4700_; lean_object* v_indicesFound_4701_; lean_object* v_newFacts_4702_; uint8_t v_inconsistent_4703_; lean_object* v_nextIdx_4704_; lean_object* v_newRawFacts_4705_; lean_object* v_facts_4706_; lean_object* v_extThms_4707_; lean_object* v_ematch_4708_; lean_object* v_inj_4709_; lean_object* v_split_4710_; lean_object* v_clean_4711_; lean_object* v_sstates_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4726_; 
v_nextDeclIdx_4695_ = lean_ctor_get(v_toGoalState_4690_, 0);
v_enodeMap_4696_ = lean_ctor_get(v_toGoalState_4690_, 1);
v_exprs_4697_ = lean_ctor_get(v_toGoalState_4690_, 2);
v_parents_4698_ = lean_ctor_get(v_toGoalState_4690_, 3);
v_congrTable_4699_ = lean_ctor_get(v_toGoalState_4690_, 4);
v_appMap_4700_ = lean_ctor_get(v_toGoalState_4690_, 5);
v_indicesFound_4701_ = lean_ctor_get(v_toGoalState_4690_, 6);
v_newFacts_4702_ = lean_ctor_get(v_toGoalState_4690_, 7);
v_inconsistent_4703_ = lean_ctor_get_uint8(v_toGoalState_4690_, sizeof(void*)*17);
v_nextIdx_4704_ = lean_ctor_get(v_toGoalState_4690_, 8);
v_newRawFacts_4705_ = lean_ctor_get(v_toGoalState_4690_, 9);
v_facts_4706_ = lean_ctor_get(v_toGoalState_4690_, 10);
v_extThms_4707_ = lean_ctor_get(v_toGoalState_4690_, 11);
v_ematch_4708_ = lean_ctor_get(v_toGoalState_4690_, 12);
v_inj_4709_ = lean_ctor_get(v_toGoalState_4690_, 13);
v_split_4710_ = lean_ctor_get(v_toGoalState_4690_, 14);
v_clean_4711_ = lean_ctor_get(v_toGoalState_4690_, 15);
v_sstates_4712_ = lean_ctor_get(v_toGoalState_4690_, 16);
v_isSharedCheck_4726_ = !lean_is_exclusive(v_toGoalState_4690_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4714_ = v_toGoalState_4690_;
v_isShared_4715_ = v_isSharedCheck_4726_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_sstates_4712_);
lean_inc(v_clean_4711_);
lean_inc(v_split_4710_);
lean_inc(v_inj_4709_);
lean_inc(v_ematch_4708_);
lean_inc(v_extThms_4707_);
lean_inc(v_facts_4706_);
lean_inc(v_newRawFacts_4705_);
lean_inc(v_nextIdx_4704_);
lean_inc(v_newFacts_4702_);
lean_inc(v_indicesFound_4701_);
lean_inc(v_appMap_4700_);
lean_inc(v_congrTable_4699_);
lean_inc(v_parents_4698_);
lean_inc(v_exprs_4697_);
lean_inc(v_enodeMap_4696_);
lean_inc(v_nextDeclIdx_4695_);
lean_dec(v_toGoalState_4690_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4726_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4719_; 
v___x_4716_ = lean_box(0);
v___x_4717_ = l_Lean_PersistentArray_push___redArg(v_facts_4706_, v_fact_4686_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 10, v___x_4717_);
v___x_4719_ = v___x_4714_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_nextDeclIdx_4695_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v_enodeMap_4696_);
lean_ctor_set(v_reuseFailAlloc_4725_, 2, v_exprs_4697_);
lean_ctor_set(v_reuseFailAlloc_4725_, 3, v_parents_4698_);
lean_ctor_set(v_reuseFailAlloc_4725_, 4, v_congrTable_4699_);
lean_ctor_set(v_reuseFailAlloc_4725_, 5, v_appMap_4700_);
lean_ctor_set(v_reuseFailAlloc_4725_, 6, v_indicesFound_4701_);
lean_ctor_set(v_reuseFailAlloc_4725_, 7, v_newFacts_4702_);
lean_ctor_set(v_reuseFailAlloc_4725_, 8, v_nextIdx_4704_);
lean_ctor_set(v_reuseFailAlloc_4725_, 9, v_newRawFacts_4705_);
lean_ctor_set(v_reuseFailAlloc_4725_, 10, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4725_, 11, v_extThms_4707_);
lean_ctor_set(v_reuseFailAlloc_4725_, 12, v_ematch_4708_);
lean_ctor_set(v_reuseFailAlloc_4725_, 13, v_inj_4709_);
lean_ctor_set(v_reuseFailAlloc_4725_, 14, v_split_4710_);
lean_ctor_set(v_reuseFailAlloc_4725_, 15, v_clean_4711_);
lean_ctor_set(v_reuseFailAlloc_4725_, 16, v_sstates_4712_);
lean_ctor_set_uint8(v_reuseFailAlloc_4725_, sizeof(void*)*17, v_inconsistent_4703_);
v___x_4719_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
lean_object* v___x_4721_; 
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 0, v___x_4719_);
v___x_4721_ = v___x_4693_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4719_);
lean_ctor_set(v_reuseFailAlloc_4724_, 1, v_mvarId_4691_);
v___x_4721_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4722_ = lean_st_ref_put(v_a_4687_, v___x_4721_);
v___x_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4716_);
return v___x_4723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4728_, v_a_4729_);
lean_dec(v_a_4729_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_){
_start:
{
lean_object* v___x_4744_; 
v___x_4744_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4732_, v_a_4733_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
lean_dec(v_a_4749_);
lean_dec_ref(v_a_4748_);
lean_dec(v_a_4747_);
lean_dec(v_a_4746_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4758_, lean_object* v_rhs_4759_, lean_object* v_proof_4760_, lean_object* v_generation_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v___x_4773_; 
lean_inc_ref(v_rhs_4759_);
lean_inc_ref(v_lhs_4758_);
v___x_4773_ = l_Lean_Meta_mkEq(v_lhs_4758_, v_rhs_4759_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4785_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc_n(v_a_4774_, 2);
lean_dec_ref_known(v___x_4773_, 1);
v___x_4775_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4774_, v_a_4762_);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4785_ == 0)
{
lean_object* v_unused_4786_; 
v_unused_4786_ = lean_ctor_get(v___x_4775_, 0);
lean_dec(v_unused_4786_);
v___x_4777_ = v___x_4775_;
v_isShared_4778_ = v_isSharedCheck_4785_;
goto v_resetjp_4776_;
}
else
{
lean_dec(v___x_4775_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4785_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4780_; 
if (v_isShared_4778_ == 0)
{
lean_ctor_set_tag(v___x_4777_, 1);
lean_ctor_set(v___x_4777_, 0, v_a_4774_);
v___x_4780_ = v___x_4777_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4774_);
v___x_4780_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
lean_object* v___x_4781_; 
lean_inc(v_a_4771_);
lean_inc_ref(v_a_4770_);
lean_inc(v_a_4769_);
lean_inc_ref(v_a_4768_);
lean_inc(v_a_4767_);
lean_inc_ref(v_a_4766_);
lean_inc(v_a_4765_);
lean_inc_ref(v_a_4764_);
lean_inc(v_a_4763_);
lean_inc(v_a_4762_);
lean_inc_ref(v___x_4780_);
lean_inc(v_generation_4761_);
lean_inc_ref(v_lhs_4758_);
v___x_4781_ = lean_grind_internalize(v_lhs_4758_, v_generation_4761_, v___x_4780_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v___x_4782_; 
lean_dec_ref_known(v___x_4781_, 1);
lean_inc(v_a_4771_);
lean_inc_ref(v_a_4770_);
lean_inc(v_a_4769_);
lean_inc_ref(v_a_4768_);
lean_inc(v_a_4767_);
lean_inc_ref(v_a_4766_);
lean_inc(v_a_4765_);
lean_inc_ref(v_a_4764_);
lean_inc(v_a_4763_);
lean_inc(v_a_4762_);
lean_inc_ref(v_rhs_4759_);
v___x_4782_ = lean_grind_internalize(v_rhs_4759_, v_generation_4761_, v___x_4780_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v___x_4783_; 
lean_dec_ref_known(v___x_4782_, 1);
v___x_4783_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4758_, v_rhs_4759_, v_proof_4760_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
return v___x_4783_;
}
else
{
lean_dec_ref(v_proof_4760_);
lean_dec_ref(v_rhs_4759_);
lean_dec_ref(v_lhs_4758_);
return v___x_4782_;
}
}
else
{
lean_dec_ref(v___x_4780_);
lean_dec(v_generation_4761_);
lean_dec_ref(v_proof_4760_);
lean_dec_ref(v_rhs_4759_);
lean_dec_ref(v_lhs_4758_);
return v___x_4781_;
}
}
}
}
else
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4794_; 
lean_dec(v_generation_4761_);
lean_dec_ref(v_proof_4760_);
lean_dec_ref(v_rhs_4759_);
lean_dec_ref(v_lhs_4758_);
v_a_4787_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4789_ = v___x_4773_;
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4773_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4792_; 
if (v_isShared_4790_ == 0)
{
v___x_4792_ = v___x_4789_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4795_, lean_object* v_rhs_4796_, lean_object* v_proof_4797_, lean_object* v_generation_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4795_, v_rhs_4796_, v_proof_4797_, v_generation_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
lean_dec(v_a_4800_);
lean_dec(v_a_4799_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4811_, lean_object* v_generation_4812_, lean_object* v_p_4813_, uint8_t v_isNeg_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4826_ = lean_box(0);
lean_inc(v_a_4824_);
lean_inc_ref(v_a_4823_);
lean_inc(v_a_4822_);
lean_inc_ref(v_a_4821_);
lean_inc(v_a_4820_);
lean_inc_ref(v_a_4819_);
lean_inc(v_a_4818_);
lean_inc_ref(v_a_4817_);
lean_inc(v_a_4816_);
lean_inc(v_a_4815_);
lean_inc_ref(v_p_4813_);
v___x_4827_ = lean_grind_internalize(v_p_4813_, v_generation_4812_, v___x_4826_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_dec_ref_known(v___x_4827_, 1);
if (v_isNeg_4814_ == 0)
{
lean_object* v___x_4828_; 
v___x_4828_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4819_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v___x_4830_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref_known(v___x_4828_, 1);
v___x_4830_ = l_Lean_Meta_mkEqTrue(v_proof_4811_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4832_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4831_);
lean_dec_ref_known(v___x_4830_, 1);
v___x_4832_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4813_, v_a_4829_, v_a_4831_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_);
return v___x_4832_;
}
else
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
lean_dec(v_a_4829_);
lean_dec_ref(v_p_4813_);
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
lean_dec_ref(v_p_4813_);
lean_dec_ref(v_proof_4811_);
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
lean_object* v___x_4849_; 
v___x_4849_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4819_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4851_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
lean_inc(v_a_4850_);
lean_dec_ref_known(v___x_4849_, 1);
v___x_4851_ = l_Lean_Meta_mkEqFalse(v_proof_4811_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4853_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4851_, 1);
v___x_4853_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4813_, v_a_4850_, v_a_4852_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_);
return v___x_4853_;
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
lean_dec(v_a_4850_);
lean_dec_ref(v_p_4813_);
v_a_4854_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4851_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4851_);
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
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4869_; 
lean_dec_ref(v_p_4813_);
lean_dec_ref(v_proof_4811_);
v_a_4862_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4864_ = v___x_4849_;
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4849_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4867_; 
if (v_isShared_4865_ == 0)
{
v___x_4867_ = v___x_4864_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4862_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
}
else
{
lean_dec_ref(v_p_4813_);
lean_dec_ref(v_proof_4811_);
return v___x_4827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4870_, lean_object* v_generation_4871_, lean_object* v_p_4872_, lean_object* v_isNeg_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
uint8_t v_isNeg_boxed_4885_; lean_object* v_res_4886_; 
v_isNeg_boxed_4885_ = lean_unbox(v_isNeg_4873_);
v_res_4886_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4870_, v_generation_4871_, v_p_4872_, v_isNeg_boxed_4885_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
lean_dec(v_a_4883_);
lean_dec_ref(v_a_4882_);
lean_dec(v_a_4881_);
lean_dec_ref(v_a_4880_);
lean_dec(v_a_4879_);
lean_dec_ref(v_a_4878_);
lean_dec(v_a_4877_);
lean_dec_ref(v_a_4876_);
lean_dec(v_a_4875_);
lean_dec(v_a_4874_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4887_, lean_object* v_generation_4888_, lean_object* v_p_4889_, lean_object* v_lhs_4890_, lean_object* v_rhs_4891_, uint8_t v_isNeg_4892_, uint8_t v_isHEq_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
if (v_isNeg_4892_ == 0)
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
lean_inc_ref(v_p_4889_);
v___x_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4905_, 0, v_p_4889_);
lean_inc(v_a_4903_);
lean_inc_ref(v_a_4902_);
lean_inc(v_a_4901_);
lean_inc_ref(v_a_4900_);
lean_inc(v_a_4899_);
lean_inc_ref(v_a_4898_);
lean_inc(v_a_4897_);
lean_inc_ref(v_a_4896_);
lean_inc(v_a_4895_);
lean_inc(v_a_4894_);
lean_inc_ref(v___x_4905_);
lean_inc(v_generation_4888_);
lean_inc_ref(v_lhs_4890_);
v___x_4906_ = lean_grind_internalize(v_lhs_4890_, v_generation_4888_, v___x_4905_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v___x_4907_; 
lean_dec_ref_known(v___x_4906_, 1);
lean_inc(v_a_4903_);
lean_inc_ref(v_a_4902_);
lean_inc(v_a_4901_);
lean_inc_ref(v_a_4900_);
lean_inc(v_a_4899_);
lean_inc_ref(v_a_4898_);
lean_inc(v_a_4897_);
lean_inc_ref(v_a_4896_);
lean_inc(v_a_4895_);
lean_inc(v_a_4894_);
lean_inc_ref(v_rhs_4891_);
v___x_4907_ = lean_grind_internalize(v_rhs_4891_, v_generation_4888_, v___x_4905_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
lean_dec_ref_known(v___x_4907_, 1);
v___x_4908_ = lean_box(0);
v___x_4909_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4889_, v___x_4908_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v___x_4910_; 
lean_dec_ref_known(v___x_4909_, 1);
v___x_4910_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4890_, v_rhs_4891_, v_proof_4887_, v_isHEq_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
return v___x_4910_;
}
else
{
lean_dec_ref(v_rhs_4891_);
lean_dec_ref(v_lhs_4890_);
lean_dec_ref(v_proof_4887_);
return v___x_4909_;
}
}
else
{
lean_dec_ref(v_rhs_4891_);
lean_dec_ref(v_lhs_4890_);
lean_dec_ref(v_p_4889_);
lean_dec_ref(v_proof_4887_);
return v___x_4907_;
}
}
else
{
lean_dec_ref_known(v___x_4905_, 1);
lean_dec_ref(v_rhs_4891_);
lean_dec_ref(v_lhs_4890_);
lean_dec_ref(v_p_4889_);
lean_dec(v_generation_4888_);
lean_dec_ref(v_proof_4887_);
return v___x_4906_;
}
}
else
{
lean_object* v___x_4911_; lean_object* v___x_4912_; 
lean_dec_ref(v_rhs_4891_);
lean_dec_ref(v_lhs_4890_);
v___x_4911_ = lean_box(0);
lean_inc(v_a_4903_);
lean_inc_ref(v_a_4902_);
lean_inc(v_a_4901_);
lean_inc_ref(v_a_4900_);
lean_inc(v_a_4899_);
lean_inc_ref(v_a_4898_);
lean_inc(v_a_4897_);
lean_inc_ref(v_a_4896_);
lean_inc(v_a_4895_);
lean_inc(v_a_4894_);
lean_inc_ref(v_p_4889_);
v___x_4912_ = lean_grind_internalize(v_p_4889_, v_generation_4888_, v___x_4911_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v___x_4913_; 
lean_dec_ref_known(v___x_4912_, 1);
v___x_4913_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4898_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v_a_4914_; lean_object* v___x_4915_; 
v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
lean_inc(v_a_4914_);
lean_dec_ref_known(v___x_4913_, 1);
v___x_4915_ = l_Lean_Meta_mkEqFalse(v_proof_4887_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4917_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4916_);
lean_dec_ref_known(v___x_4915_, 1);
v___x_4917_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4889_, v_a_4914_, v_a_4916_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_);
return v___x_4917_;
}
else
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
lean_dec(v_a_4914_);
lean_dec_ref(v_p_4889_);
v_a_4918_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4915_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4915_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
}
else
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4933_; 
lean_dec_ref(v_p_4889_);
lean_dec_ref(v_proof_4887_);
v_a_4926_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4928_ = v___x_4913_;
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4913_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4931_; 
if (v_isShared_4929_ == 0)
{
v___x_4931_ = v___x_4928_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_a_4926_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
}
else
{
lean_dec_ref(v_p_4889_);
lean_dec_ref(v_proof_4887_);
return v___x_4912_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4934_ = _args[0];
lean_object* v_generation_4935_ = _args[1];
lean_object* v_p_4936_ = _args[2];
lean_object* v_lhs_4937_ = _args[3];
lean_object* v_rhs_4938_ = _args[4];
lean_object* v_isNeg_4939_ = _args[5];
lean_object* v_isHEq_4940_ = _args[6];
lean_object* v_a_4941_ = _args[7];
lean_object* v_a_4942_ = _args[8];
lean_object* v_a_4943_ = _args[9];
lean_object* v_a_4944_ = _args[10];
lean_object* v_a_4945_ = _args[11];
lean_object* v_a_4946_ = _args[12];
lean_object* v_a_4947_ = _args[13];
lean_object* v_a_4948_ = _args[14];
lean_object* v_a_4949_ = _args[15];
lean_object* v_a_4950_ = _args[16];
lean_object* v_a_4951_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4952_; uint8_t v_isHEq_boxed_4953_; lean_object* v_res_4954_; 
v_isNeg_boxed_4952_ = lean_unbox(v_isNeg_4939_);
v_isHEq_boxed_4953_ = lean_unbox(v_isHEq_4940_);
v_res_4954_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4934_, v_generation_4935_, v_p_4936_, v_lhs_4937_, v_rhs_4938_, v_isNeg_boxed_4952_, v_isHEq_boxed_4953_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_);
lean_dec(v_a_4950_);
lean_dec_ref(v_a_4949_);
lean_dec(v_a_4948_);
lean_dec_ref(v_a_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_a_4945_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
lean_dec(v_a_4942_);
lean_dec(v_a_4941_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4958_, lean_object* v_generation_4959_, lean_object* v_p_4960_, uint8_t v_isNeg_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_){
_start:
{
lean_object* v___x_4973_; 
lean_inc_ref(v_p_4960_);
v___x_4973_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4960_, v_a_4969_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; lean_object* v___x_4975_; uint8_t v___x_4976_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
lean_inc(v_a_4974_);
lean_dec_ref_known(v___x_4973_, 1);
v___x_4975_ = l_Lean_Expr_cleanupAnnotations(v_a_4974_);
v___x_4976_ = l_Lean_Expr_isApp(v___x_4975_);
if (v___x_4976_ == 0)
{
lean_object* v___x_4977_; 
lean_dec_ref(v___x_4975_);
v___x_4977_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4958_, v_generation_4959_, v_p_4960_, v_isNeg_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
return v___x_4977_;
}
else
{
lean_object* v_arg_4978_; lean_object* v___x_4979_; uint8_t v___x_4980_; 
v_arg_4978_ = lean_ctor_get(v___x_4975_, 1);
lean_inc_ref(v_arg_4978_);
v___x_4979_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4975_);
v___x_4980_ = l_Lean_Expr_isApp(v___x_4979_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; 
lean_dec_ref(v___x_4979_);
lean_dec_ref(v_arg_4978_);
v___x_4981_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4958_, v_generation_4959_, v_p_4960_, v_isNeg_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
return v___x_4981_;
}
else
{
lean_object* v_arg_4982_; lean_object* v___x_4983_; uint8_t v___x_4984_; 
v_arg_4982_ = lean_ctor_get(v___x_4979_, 1);
lean_inc_ref(v_arg_4982_);
v___x_4983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4979_);
v___x_4984_ = l_Lean_Expr_isApp(v___x_4983_);
if (v___x_4984_ == 0)
{
lean_object* v___x_4985_; 
lean_dec_ref(v___x_4983_);
lean_dec_ref(v_arg_4982_);
lean_dec_ref(v_arg_4978_);
v___x_4985_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4958_, v_generation_4959_, v_p_4960_, v_isNeg_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
return v___x_4985_;
}
else
{
lean_object* v_arg_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; uint8_t v___x_4989_; 
v_arg_4986_ = lean_ctor_get(v___x_4983_, 1);
lean_inc_ref(v_arg_4986_);
v___x_4987_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4983_);
v___x_4988_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_4989_ = l_Lean_Expr_isConstOf(v___x_4987_, v___x_4988_);
if (v___x_4989_ == 0)
{
uint8_t v___x_4990_; 
lean_dec_ref(v_arg_4982_);
v___x_4990_ = l_Lean_Expr_isApp(v___x_4987_);
if (v___x_4990_ == 0)
{
lean_object* v___x_4991_; 
lean_dec_ref(v___x_4987_);
lean_dec_ref(v_arg_4986_);
lean_dec_ref(v_arg_4978_);
v___x_4991_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4958_, v_generation_4959_, v_p_4960_, v_isNeg_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
return v___x_4991_;
}
else
{
lean_object* v___x_4992_; lean_object* v___x_4993_; uint8_t v___x_4994_; 
v___x_4992_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4987_);
v___x_4993_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_4994_ = l_Lean_Expr_isConstOf(v___x_4992_, v___x_4993_);
lean_dec_ref(v___x_4992_);
if (v___x_4994_ == 0)
{
lean_object* v___x_4995_; 
lean_dec_ref(v_arg_4986_);
lean_dec_ref(v_arg_4978_);
v___x_4995_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4958_, v_generation_4959_, v_p_4960_, v_isNeg_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
return v___x_4995_;
}
else
{
lean_object* v___x_4996_; 
v___x_4996_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4958_, v_generation_4959_, v_p_4960_, v_arg_4986_, v_arg_4978_, v_isNeg_4961_, v___x_4994_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
return v___x_4996_;
}
}
}
else
{
uint8_t v___x_4997_; 
lean_dec_ref(v___x_4987_);
v___x_4997_ = l_Lean_Expr_isProp(v_arg_4986_);
lean_dec_ref(v_arg_4986_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; 
v___x_4998_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4958_, v_generation_4959_, v_p_4960_, v_arg_4982_, v_arg_4978_, v_isNeg_4961_, v___x_4997_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
return v___x_4998_;
}
else
{
lean_object* v___x_4999_; 
lean_dec_ref(v_arg_4982_);
lean_dec_ref(v_arg_4978_);
v___x_4999_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4958_, v_generation_4959_, v_p_4960_, v_isNeg_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_);
return v___x_4999_;
}
}
}
}
}
}
else
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
lean_dec_ref(v_p_4960_);
lean_dec(v_generation_4959_);
lean_dec_ref(v_proof_4958_);
v_a_5000_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5002_ = v___x_4973_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4973_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5008_, lean_object* v_generation_5009_, lean_object* v_p_5010_, lean_object* v_isNeg_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_){
_start:
{
uint8_t v_isNeg_boxed_5023_; lean_object* v_res_5024_; 
v_isNeg_boxed_5023_ = lean_unbox(v_isNeg_5011_);
v_res_5024_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5008_, v_generation_5009_, v_p_5010_, v_isNeg_boxed_5023_, v_a_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_);
lean_dec(v_a_5021_);
lean_dec_ref(v_a_5020_);
lean_dec(v_a_5019_);
lean_dec_ref(v_a_5018_);
lean_dec(v_a_5017_);
lean_dec_ref(v_a_5016_);
lean_dec(v_a_5015_);
lean_dec_ref(v_a_5014_);
lean_dec(v_a_5013_);
lean_dec(v_a_5012_);
return v_res_5024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5032_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5033_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5034_ = l_Lean_Name_append(v___x_5033_, v___x_5032_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5035_, lean_object* v_proof_5036_, lean_object* v_generation_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_){
_start:
{
lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v___y_5052_; lean_object* v___y_5053_; lean_object* v___y_5054_; lean_object* v___y_5055_; lean_object* v___y_5056_; lean_object* v___y_5057_; lean_object* v___y_5058_; lean_object* v___y_5059_; lean_object* v___y_5063_; lean_object* v___y_5064_; lean_object* v___y_5065_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5072_; lean_object* v___x_5080_; lean_object* v_toCold_5081_; lean_object* v_options_5082_; uint8_t v_hasTrace_5083_; 
lean_inc_ref(v_fact_5035_);
v___x_5080_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5035_, v_a_5038_);
lean_dec_ref(v___x_5080_);
v_toCold_5081_ = lean_ctor_get(v_a_5046_, 0);
v_options_5082_ = lean_ctor_get(v_toCold_5081_, 2);
v_hasTrace_5083_ = lean_ctor_get_uint8(v_options_5082_, sizeof(void*)*1);
if (v_hasTrace_5083_ == 0)
{
v___y_5063_ = v_a_5038_;
v___y_5064_ = v_a_5039_;
v___y_5065_ = v_a_5040_;
v___y_5066_ = v_a_5041_;
v___y_5067_ = v_a_5042_;
v___y_5068_ = v_a_5043_;
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
v___y_5072_ = v_a_5047_;
goto v___jp_5062_;
}
else
{
lean_object* v_inheritedTraceOptions_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; uint8_t v___x_5087_; 
v_inheritedTraceOptions_5084_ = lean_ctor_get(v_toCold_5081_, 11);
v___x_5085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5087_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5084_, v_options_5082_, v___x_5086_);
if (v___x_5087_ == 0)
{
v___y_5063_ = v_a_5038_;
v___y_5064_ = v_a_5039_;
v___y_5065_ = v_a_5040_;
v___y_5066_ = v_a_5041_;
v___y_5067_ = v_a_5042_;
v___y_5068_ = v_a_5043_;
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
v___y_5072_ = v_a_5047_;
goto v___jp_5062_;
}
else
{
lean_object* v___x_5088_; 
v___x_5088_ = l_Lean_Meta_Grind_updateLastTag(v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v___x_5089_; lean_object* v___x_5090_; 
lean_dec_ref_known(v___x_5088_, 1);
lean_inc_ref(v_fact_5035_);
v___x_5089_ = l_Lean_MessageData_ofExpr(v_fact_5035_);
v___x_5090_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5085_, v___x_5089_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_dec_ref_known(v___x_5090_, 1);
v___y_5063_ = v_a_5038_;
v___y_5064_ = v_a_5039_;
v___y_5065_ = v_a_5040_;
v___y_5066_ = v_a_5041_;
v___y_5067_ = v_a_5042_;
v___y_5068_ = v_a_5043_;
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
v___y_5072_ = v_a_5047_;
goto v___jp_5062_;
}
else
{
lean_dec(v_generation_5037_);
lean_dec_ref(v_proof_5036_);
lean_dec_ref(v_fact_5035_);
return v___x_5090_;
}
}
else
{
lean_dec(v_generation_5037_);
lean_dec_ref(v_proof_5036_);
lean_dec_ref(v_fact_5035_);
return v___x_5088_;
}
}
}
v___jp_5049_:
{
uint8_t v___x_5060_; lean_object* v___x_5061_; 
v___x_5060_ = 0;
v___x_5061_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5036_, v_generation_5037_, v_fact_5035_, v___x_5060_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_);
return v___x_5061_;
}
v___jp_5062_:
{
lean_object* v___x_5073_; uint8_t v___x_5074_; 
lean_inc_ref(v_fact_5035_);
v___x_5073_ = l_Lean_Expr_cleanupAnnotations(v_fact_5035_);
v___x_5074_ = l_Lean_Expr_isApp(v___x_5073_);
if (v___x_5074_ == 0)
{
lean_dec_ref(v___x_5073_);
v___y_5050_ = v___y_5063_;
v___y_5051_ = v___y_5064_;
v___y_5052_ = v___y_5065_;
v___y_5053_ = v___y_5066_;
v___y_5054_ = v___y_5067_;
v___y_5055_ = v___y_5068_;
v___y_5056_ = v___y_5069_;
v___y_5057_ = v___y_5070_;
v___y_5058_ = v___y_5071_;
v___y_5059_ = v___y_5072_;
goto v___jp_5049_;
}
else
{
lean_object* v_arg_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; uint8_t v___x_5078_; 
v_arg_5075_ = lean_ctor_get(v___x_5073_, 1);
lean_inc_ref(v_arg_5075_);
v___x_5076_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5073_);
v___x_5077_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5078_ = l_Lean_Expr_isConstOf(v___x_5076_, v___x_5077_);
lean_dec_ref(v___x_5076_);
if (v___x_5078_ == 0)
{
lean_dec_ref(v_arg_5075_);
v___y_5050_ = v___y_5063_;
v___y_5051_ = v___y_5064_;
v___y_5052_ = v___y_5065_;
v___y_5053_ = v___y_5066_;
v___y_5054_ = v___y_5067_;
v___y_5055_ = v___y_5068_;
v___y_5056_ = v___y_5069_;
v___y_5057_ = v___y_5070_;
v___y_5058_ = v___y_5071_;
v___y_5059_ = v___y_5072_;
goto v___jp_5049_;
}
else
{
lean_object* v___x_5079_; 
lean_dec_ref(v_fact_5035_);
v___x_5079_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5036_, v_generation_5037_, v_arg_5075_, v___x_5078_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_);
return v___x_5079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5091_, lean_object* v_proof_5092_, lean_object* v_generation_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5091_, v_proof_5092_, v_generation_5093_, v_a_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_, v_a_5103_);
lean_dec(v_a_5103_);
lean_dec_ref(v_a_5102_);
lean_dec(v_a_5101_);
lean_dec_ref(v_a_5100_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
lean_dec(v_a_5095_);
lean_dec(v_a_5094_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
lean_object* v___x_5120_; 
v___x_5120_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5109_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_object* v_a_5121_; uint8_t v___x_5122_; 
v_a_5121_ = lean_ctor_get(v___x_5120_, 0);
lean_inc(v_a_5121_);
lean_dec_ref_known(v___x_5120_, 1);
v___x_5122_ = lean_unbox(v_a_5121_);
lean_dec(v_a_5121_);
if (v___x_5122_ == 0)
{
lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5123_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5124_ = l_Lean_Core_checkSystem(v___x_5123_, v___y_5117_, v___y_5118_);
if (lean_obj_tag(v___x_5124_) == 0)
{
lean_object* v___x_5125_; 
lean_dec_ref_known(v___x_5124_, 1);
v___x_5125_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5109_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5162_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5128_ = v___x_5125_;
v_isShared_5129_ = v_isSharedCheck_5162_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5125_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5162_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
if (lean_obj_tag(v_a_5126_) == 1)
{
lean_object* v_val_5130_; 
lean_del_object(v___x_5128_);
v_val_5130_ = lean_ctor_get(v_a_5126_, 0);
lean_inc(v_val_5130_);
lean_dec_ref_known(v_a_5126_, 1);
if (lean_obj_tag(v_val_5130_) == 0)
{
lean_object* v_lhs_5131_; lean_object* v_rhs_5132_; lean_object* v_proof_5133_; uint8_t v_isHEq_5134_; lean_object* v___x_5135_; 
v_lhs_5131_ = lean_ctor_get(v_val_5130_, 0);
lean_inc_ref(v_lhs_5131_);
v_rhs_5132_ = lean_ctor_get(v_val_5130_, 1);
lean_inc_ref(v_rhs_5132_);
v_proof_5133_ = lean_ctor_get(v_val_5130_, 2);
lean_inc_ref(v_proof_5133_);
v_isHEq_5134_ = lean_ctor_get_uint8(v_val_5130_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5130_, 3);
v___x_5135_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5131_, v_rhs_5132_, v_proof_5133_, v_isHEq_5134_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_);
if (lean_obj_tag(v___x_5135_) == 0)
{
lean_dec_ref_known(v___x_5135_, 1);
goto _start;
}
else
{
lean_object* v_a_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
v_a_5137_ = lean_ctor_get(v___x_5135_, 0);
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5135_);
if (v_isSharedCheck_5144_ == 0)
{
v___x_5139_ = v___x_5135_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_a_5137_);
lean_dec(v___x_5135_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5137_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
}
else
{
lean_object* v_prop_5145_; lean_object* v_proof_5146_; lean_object* v_generation_5147_; lean_object* v___x_5148_; 
v_prop_5145_ = lean_ctor_get(v_val_5130_, 0);
lean_inc_ref(v_prop_5145_);
v_proof_5146_ = lean_ctor_get(v_val_5130_, 1);
lean_inc_ref(v_proof_5146_);
v_generation_5147_ = lean_ctor_get(v_val_5130_, 2);
lean_inc(v_generation_5147_);
lean_dec_ref_known(v_val_5130_, 3);
v___x_5148_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5145_, v_proof_5146_, v_generation_5147_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_dec_ref_known(v___x_5148_, 1);
goto _start;
}
else
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
v_a_5150_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5152_ = v___x_5148_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5148_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
if (v_isShared_5153_ == 0)
{
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_a_5150_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
}
else
{
lean_object* v___x_5158_; lean_object* v___x_5160_; 
lean_dec(v_a_5126_);
v___x_5158_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 0, v___x_5158_);
v___x_5160_ = v___x_5128_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v___x_5158_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
else
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5170_; 
v_a_5163_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5165_ = v___x_5125_;
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5125_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5168_; 
if (v_isShared_5166_ == 0)
{
v___x_5168_ = v___x_5165_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
}
}
else
{
lean_object* v_a_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5178_; 
v_a_5171_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5173_ = v___x_5124_;
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_a_5171_);
lean_dec(v___x_5124_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___x_5176_; 
if (v_isShared_5174_ == 0)
{
v___x_5176_ = v___x_5173_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
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
lean_object* v___x_5179_; 
v___x_5179_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5109_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5187_; 
v_isSharedCheck_5187_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5187_ == 0)
{
lean_object* v_unused_5188_; 
v_unused_5188_ = lean_ctor_get(v___x_5179_, 0);
lean_dec(v_unused_5188_);
v___x_5181_ = v___x_5179_;
v_isShared_5182_ = v_isSharedCheck_5187_;
goto v_resetjp_5180_;
}
else
{
lean_dec(v___x_5179_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5187_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5183_; lean_object* v___x_5185_; 
v___x_5183_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5182_ == 0)
{
lean_ctor_set(v___x_5181_, 0, v___x_5183_);
v___x_5185_ = v___x_5181_;
goto v_reusejp_5184_;
}
else
{
lean_object* v_reuseFailAlloc_5186_; 
v_reuseFailAlloc_5186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5186_, 0, v___x_5183_);
v___x_5185_ = v_reuseFailAlloc_5186_;
goto v_reusejp_5184_;
}
v_reusejp_5184_:
{
return v___x_5185_;
}
}
}
else
{
lean_object* v_a_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5196_; 
v_a_5189_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5196_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5196_ == 0)
{
v___x_5191_ = v___x_5179_;
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_a_5189_);
lean_dec(v___x_5179_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5196_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
lean_object* v___x_5194_; 
if (v_isShared_5192_ == 0)
{
v___x_5194_ = v___x_5191_;
goto v_reusejp_5193_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_a_5189_);
v___x_5194_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5193_;
}
v_reusejp_5193_:
{
return v___x_5194_;
}
}
}
}
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
v_a_5197_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5120_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5120_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
lean_object* v_res_5216_; 
v_res_5216_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
lean_dec(v___y_5208_);
lean_dec_ref(v___y_5207_);
lean_dec(v___y_5206_);
lean_dec(v___y_5205_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_){
_start:
{
lean_object* v___x_5228_; lean_object* v___x_5229_; 
v___x_5228_ = lean_box(0);
v___x_5229_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
lean_dec(v_a_5226_);
lean_dec_ref(v_a_5225_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
lean_dec(v_a_5222_);
lean_dec_ref(v_a_5221_);
lean_dec(v_a_5220_);
lean_dec_ref(v_a_5219_);
lean_dec(v_a_5218_);
lean_dec(v_a_5217_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5242_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5232_ = v___x_5229_;
v_isShared_5233_ = v_isSharedCheck_5242_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5229_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5242_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v_fst_5234_; 
v_fst_5234_ = lean_ctor_get(v_a_5230_, 0);
lean_inc(v_fst_5234_);
lean_dec(v_a_5230_);
if (lean_obj_tag(v_fst_5234_) == 0)
{
lean_object* v___x_5236_; 
if (v_isShared_5233_ == 0)
{
lean_ctor_set(v___x_5232_, 0, v___x_5228_);
v___x_5236_ = v___x_5232_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5228_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
return v___x_5236_;
}
}
else
{
lean_object* v_val_5238_; lean_object* v___x_5240_; 
v_val_5238_ = lean_ctor_get(v_fst_5234_, 0);
lean_inc(v_val_5238_);
lean_dec_ref_known(v_fst_5234_, 1);
if (v_isShared_5233_ == 0)
{
lean_ctor_set(v___x_5232_, 0, v_val_5238_);
v___x_5240_ = v___x_5232_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_val_5238_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
}
else
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5250_; 
v_a_5243_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5229_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5229_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5248_; 
if (v_isShared_5246_ == 0)
{
v___x_5248_ = v___x_5245_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_a_5243_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
return v___x_5248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = lean_grind_process_new_facts(v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_inst_5263_, lean_object* v_a_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
lean_object* v___x_5276_; 
v___x_5276_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_);
return v___x_5276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_inst_5277_, lean_object* v_a_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
lean_object* v_res_5290_; 
v_res_5290_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_inst_5277_, v_a_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v___y_5286_);
lean_dec_ref(v___y_5285_);
lean_dec(v___y_5284_);
lean_dec_ref(v___y_5283_);
lean_dec(v___y_5282_);
lean_dec_ref(v___y_5281_);
lean_dec(v___y_5280_);
lean_dec(v___y_5279_);
lean_dec_ref(v_a_5278_);
return v_res_5290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5291_, lean_object* v_proof_5292_, lean_object* v_generation_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_){
_start:
{
uint8_t v___x_5305_; 
lean_inc_ref(v_fact_5291_);
v___x_5305_ = l_Lean_Expr_isTrue(v_fact_5291_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; 
v___x_5306_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5294_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_object* v_a_5307_; lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5318_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5318_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5318_ == 0)
{
v___x_5309_ = v___x_5306_;
v_isShared_5310_ = v_isSharedCheck_5318_;
goto v_resetjp_5308_;
}
else
{
lean_inc(v_a_5307_);
lean_dec(v___x_5306_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5318_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
uint8_t v___x_5311_; 
v___x_5311_ = lean_unbox(v_a_5307_);
lean_dec(v_a_5307_);
if (v___x_5311_ == 0)
{
lean_object* v___x_5312_; lean_object* v___x_5313_; 
lean_del_object(v___x_5309_);
v___x_5312_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5294_);
lean_dec_ref(v___x_5312_);
v___x_5313_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5291_, v_proof_5292_, v_generation_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
return v___x_5313_;
}
else
{
lean_object* v___x_5314_; lean_object* v___x_5316_; 
lean_dec(v_generation_5293_);
lean_dec_ref(v_proof_5292_);
lean_dec_ref(v_fact_5291_);
v___x_5314_ = lean_box(0);
if (v_isShared_5310_ == 0)
{
lean_ctor_set(v___x_5309_, 0, v___x_5314_);
v___x_5316_ = v___x_5309_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v___x_5314_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
}
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5326_; 
lean_dec(v_generation_5293_);
lean_dec_ref(v_proof_5292_);
lean_dec_ref(v_fact_5291_);
v_a_5319_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5321_ = v___x_5306_;
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
else
{
lean_inc(v_a_5319_);
lean_dec(v___x_5306_);
v___x_5321_ = lean_box(0);
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
v_resetjp_5320_:
{
lean_object* v___x_5324_; 
if (v_isShared_5322_ == 0)
{
v___x_5324_ = v___x_5321_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
}
else
{
lean_object* v___x_5327_; lean_object* v___x_5328_; 
lean_dec(v_generation_5293_);
lean_dec_ref(v_proof_5292_);
lean_dec_ref(v_fact_5291_);
v___x_5327_ = lean_box(0);
v___x_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5327_);
return v___x_5328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5329_, lean_object* v_proof_5330_, lean_object* v_generation_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_){
_start:
{
lean_object* v_res_5343_; 
v_res_5343_ = l_Lean_Meta_Grind_add(v_fact_5329_, v_proof_5330_, v_generation_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_);
lean_dec(v_a_5341_);
lean_dec_ref(v_a_5340_);
lean_dec(v_a_5339_);
lean_dec_ref(v_a_5338_);
lean_dec(v_a_5337_);
lean_dec_ref(v_a_5336_);
lean_dec(v_a_5335_);
lean_dec_ref(v_a_5334_);
lean_dec(v_a_5333_);
lean_dec(v_a_5332_);
return v_res_5343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5344_, lean_object* v_generation_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_){
_start:
{
lean_object* v___x_5357_; 
lean_inc(v_fvarId_5344_);
v___x_5357_ = l_Lean_FVarId_getType___redArg(v_fvarId_5344_, v_a_5352_, v_a_5354_, v_a_5355_);
if (lean_obj_tag(v___x_5357_) == 0)
{
lean_object* v_a_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; 
v_a_5358_ = lean_ctor_get(v___x_5357_, 0);
lean_inc(v_a_5358_);
lean_dec_ref_known(v___x_5357_, 1);
v___x_5359_ = l_Lean_mkFVar(v_fvarId_5344_);
v___x_5360_ = l_Lean_Meta_Grind_add(v_a_5358_, v___x_5359_, v_generation_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_);
return v___x_5360_;
}
else
{
lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5368_; 
lean_dec(v_generation_5345_);
lean_dec(v_fvarId_5344_);
v_a_5361_ = lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5363_ = v___x_5357_;
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5357_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5369_, lean_object* v_generation_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_, lean_object* v_a_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_, lean_object* v_a_5381_){
_start:
{
lean_object* v_res_5382_; 
v_res_5382_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5369_, v_generation_5370_, v_a_5371_, v_a_5372_, v_a_5373_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_, v_a_5380_);
lean_dec(v_a_5380_);
lean_dec_ref(v_a_5379_);
lean_dec(v_a_5378_);
lean_dec_ref(v_a_5377_);
lean_dec(v_a_5376_);
lean_dec_ref(v_a_5375_);
lean_dec(v_a_5374_);
lean_dec_ref(v_a_5373_);
lean_dec(v_a_5372_);
lean_dec(v_a_5371_);
return v_res_5382_;
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
