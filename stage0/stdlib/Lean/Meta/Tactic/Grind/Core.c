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
uint64_t lean_usize_to_uint64(size_t);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
v_options_169_ = lean_ctor_get(v___y_161_, 1);
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
v_ref_192_ = lean_ctor_get(v___y_189_, 4);
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
v___x_229_ = lean_st_ref_put(v___y_190_, v___x_228_);
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
size_t v_x_22454__boxed_351_; lean_object* v_res_352_; 
v_x_22454__boxed_351_ = lean_unbox_usize(v_x_349_);
lean_dec(v_x_349_);
v_res_352_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_347_, v_x_348_, v_x_22454__boxed_351_, v_x_350_);
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
lean_object* v_head_393_; lean_object* v_tail_394_; lean_object* v___x_395_; lean_object* v___y_397_; uint8_t v_a_437_; uint8_t v___x_451_; 
v_head_393_ = lean_ctor_get(v_as_x27_379_, 0);
v_tail_394_ = lean_ctor_get(v_as_x27_379_, 1);
v___x_395_ = lean_box(0);
v___x_451_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_393_);
if (v___x_451_ == 0)
{
v_a_437_ = v___x_451_;
goto v___jp_436_;
}
else
{
lean_object* v___x_452_; 
lean_inc(v_head_393_);
v___x_452_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_393_, v___y_381_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; uint8_t v___x_454_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v___x_454_ = lean_unbox(v_a_453_);
lean_dec(v_a_453_);
v_a_437_ = v___x_454_;
goto v___jp_436_;
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_455_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_452_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_452_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
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
v___x_430_ = lean_st_ref_put(v___y_397_, v___x_429_);
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
v_options_439_ = lean_ctor_get(v___y_389_, 1);
v_hasTrace_440_ = lean_ctor_get_uint8(v_options_439_, sizeof(void*)*1);
if (v_hasTrace_440_ == 0)
{
v___y_397_ = v___y_381_;
goto v___jp_396_;
}
else
{
lean_object* v_toCold_441_; lean_object* v_inheritedTraceOptions_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v_toCold_441_ = lean_ctor_get(v___y_389_, 0);
v_inheritedTraceOptions_442_ = lean_ctor_get(v_toCold_441_, 4);
v___x_443_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_444_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_445_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_442_, v_options_439_, v___x_444_);
if (v___x_445_ == 0)
{
v___y_397_ = v___y_381_;
goto v___jp_396_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_Grind_updateLastTag(v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec_ref_known(v___x_446_, 1);
v___x_447_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__8);
lean_inc(v_head_393_);
v___x_448_ = l_Lean_MessageData_ofExpr(v_head_393_);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_443_, v___x_449_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_dec_ref_known(v___x_450_, 1);
v___y_397_ = v___y_381_;
goto v___jp_396_;
}
else
{
return v___x_450_;
}
}
else
{
return v___x_446_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___boxed(lean_object* v_as_x27_463_, lean_object* v_b_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_463_, v_b_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec(v___y_465_);
lean_dec(v_as_x27_463_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(lean_object* v_root_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Meta_Grind_getParents___redArg(v_root_477_, v_a_478_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v___x_491_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_490_);
v___x_492_ = lean_box(0);
v___x_493_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v___x_491_, v___x_492_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
lean_dec(v___x_491_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v___x_493_, 0);
lean_dec(v_unused_501_);
v___x_495_ = v___x_493_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_dec(v___x_493_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v_a_490_);
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_490_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_a_490_);
v_a_502_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_493_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_493_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents___boxed(lean_object* v_root_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_root_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_root_510_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(lean_object* v___x_523_, lean_object* v_00_u03b2_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___redArg(v___x_523_, v_x_525_, v_x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0___boxed(lean_object* v___x_528_, lean_object* v_00_u03b2_529_, lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0(v___x_528_, v_00_u03b2_529_, v_x_530_, v_x_531_);
lean_dec_ref(v___x_528_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(lean_object* v_cls_533_, lean_object* v_msg_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_533_, v_msg_534_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___boxed(lean_object* v_cls_547_, lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1(v_cls_547_, v_msg_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec(v___y_549_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(lean_object* v_as_561_, lean_object* v_as_x27_562_, lean_object* v_b_563_, lean_object* v_a_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg(v_as_x27_562_, v_b_563_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___boxed(lean_object* v_as_577_, lean_object* v_as_x27_578_, lean_object* v_b_579_, lean_object* v_a_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2(v_as_577_, v_as_x27_578_, v_b_579_, v_a_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec(v___y_581_);
lean_dec(v_as_x27_578_);
lean_dec(v_as_577_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(lean_object* v___x_593_, lean_object* v_00_u03b2_594_, lean_object* v_x_595_, size_t v_x_596_, lean_object* v_x_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_593_, v_x_595_, v_x_596_, v_x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___boxed(lean_object* v___x_599_, lean_object* v_00_u03b2_600_, lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
size_t v_x_22916__boxed_604_; lean_object* v_res_605_; 
v_x_22916__boxed_604_ = lean_unbox_usize(v_x_602_);
lean_dec(v_x_602_);
v_res_605_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_599_, v_00_u03b2_600_, v_x_601_, v_x_22916__boxed_604_, v_x_603_);
lean_dec_ref(v___x_599_);
return v_res_605_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__0));
v___x_608_ = l_Lean_stringToMessageData(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(lean_object* v_as_x27_609_, lean_object* v_b_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
if (lean_obj_tag(v_as_x27_609_) == 0)
{
lean_object* v___x_622_; 
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v_b_610_);
return v___x_622_;
}
else
{
lean_object* v_head_623_; lean_object* v_tail_624_; lean_object* v___x_625_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; uint8_t v_a_640_; uint8_t v___x_654_; 
v_head_623_ = lean_ctor_get(v_as_x27_609_, 0);
v_tail_624_ = lean_ctor_get(v_as_x27_609_, 1);
v___x_625_ = lean_box(0);
v___x_654_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_isCongrRelevant(v_head_623_);
if (v___x_654_ == 0)
{
v_a_640_ = v___x_654_;
goto v___jp_639_;
}
else
{
lean_object* v___x_655_; 
lean_inc(v_head_623_);
v___x_655_ = l_Lean_Meta_Grind_isCongrRoot___redArg(v_head_623_, v___y_611_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; uint8_t v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = lean_unbox(v_a_656_);
lean_dec(v_a_656_);
v_a_640_ = v___x_657_;
goto v___jp_639_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
v_a_658_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_655_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_655_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
v___jp_626_:
{
lean_object* v___x_637_; 
lean_inc(v_head_623_);
v___x_637_ = l_Lean_Meta_Grind_addCongrTable(v_head_623_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_dec_ref_known(v___x_637_, 1);
v_as_x27_609_ = v_tail_624_;
v_b_610_ = v___x_625_;
goto _start;
}
else
{
return v___x_637_;
}
}
v___jp_639_:
{
if (v_a_640_ == 0)
{
v_as_x27_609_ = v_tail_624_;
v_b_610_ = v___x_625_;
goto _start;
}
else
{
lean_object* v_options_642_; uint8_t v_hasTrace_643_; 
v_options_642_ = lean_ctor_get(v___y_619_, 1);
v_hasTrace_643_ = lean_ctor_get_uint8(v_options_642_, sizeof(void*)*1);
if (v_hasTrace_643_ == 0)
{
v___y_627_ = v___y_611_;
v___y_628_ = v___y_612_;
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
goto v___jp_626_;
}
else
{
lean_object* v_toCold_644_; lean_object* v_inheritedTraceOptions_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_toCold_644_ = lean_ctor_get(v___y_619_, 0);
v_inheritedTraceOptions_645_ = lean_ctor_get(v_toCold_644_, 4);
v___x_646_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__3));
v___x_647_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__6);
v___x_648_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_645_, v_options_642_, v___x_647_);
if (v___x_648_ == 0)
{
v___y_627_ = v___y_611_;
v___y_628_ = v___y_612_;
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
goto v___jp_626_;
}
else
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Meta_Grind_updateLastTag(v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec_ref_known(v___x_649_, 1);
v___x_650_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___closed__1);
lean_inc(v_head_623_);
v___x_651_ = l_Lean_MessageData_ofExpr(v_head_623_);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_646_, v___x_652_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_dec_ref_known(v___x_653_, 1);
v___y_627_ = v___y_611_;
v___y_628_ = v___y_612_;
v___y_629_ = v___y_613_;
v___y_630_ = v___y_614_;
v___y_631_ = v___y_615_;
v___y_632_ = v___y_616_;
v___y_633_ = v___y_617_;
v___y_634_ = v___y_618_;
v___y_635_ = v___y_619_;
v___y_636_ = v___y_620_;
goto v___jp_626_;
}
else
{
return v___x_653_;
}
}
else
{
return v___x_649_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg___boxed(lean_object* v_as_x27_666_, lean_object* v_b_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_666_, v_b_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec(v___y_668_);
lean_dec(v_as_x27_666_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(lean_object* v_parents_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = l_Lean_Meta_Grind_ParentSet_elems(v_parents_680_);
v___x_693_ = lean_box(0);
v___x_694_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v___x_692_, v___x_693_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v___x_692_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v___x_694_, 0);
lean_dec(v_unused_702_);
v___x_696_ = v___x_694_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_dec(v___x_694_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_693_);
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_693_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents___boxed(lean_object* v_parents_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v_parents_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec(v_a_704_);
lean_dec(v_parents_703_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(lean_object* v_as_716_, lean_object* v_as_x27_717_, lean_object* v_b_718_, lean_object* v_a_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___redArg(v_as_x27_717_, v_b_718_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0___boxed(lean_object* v_as_732_, lean_object* v_as_x27_733_, lean_object* v_b_734_, lean_object* v_a_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents_spec__0(v_as_732_, v_as_x27_733_, v_b_734_, v_a_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
lean_dec(v_as_x27_733_);
lean_dec(v_as_732_);
return v_res_747_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_748_, lean_object* v_i_749_, lean_object* v_k_750_){
_start:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_array_get_size(v_keys_748_);
v___x_752_ = lean_nat_dec_lt(v_i_749_, v___x_751_);
if (v___x_752_ == 0)
{
lean_dec(v_i_749_);
return v___x_752_;
}
else
{
lean_object* v_k_x27_753_; uint8_t v___x_754_; 
v_k_x27_753_ = lean_array_fget_borrowed(v_keys_748_, v_i_749_);
v___x_754_ = l_Lean_instBEqMVarId_beq(v_k_750_, v_k_x27_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_add(v_i_749_, v___x_755_);
lean_dec(v_i_749_);
v_i_749_ = v___x_756_;
goto _start;
}
else
{
lean_dec(v_i_749_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_758_, lean_object* v_i_759_, lean_object* v_k_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_758_, v_i_759_, v_k_760_);
lean_dec(v_k_760_);
lean_dec_ref(v_keys_758_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(lean_object* v_x_763_, size_t v_x_764_, lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
lean_object* v_es_766_; lean_object* v___x_767_; size_t v___x_768_; size_t v___x_769_; lean_object* v_j_770_; lean_object* v___x_771_; 
v_es_766_ = lean_ctor_get(v_x_763_, 0);
v___x_767_ = lean_box(2);
v___x_768_ = ((size_t)31ULL);
v___x_769_ = lean_usize_land(v_x_764_, v___x_768_);
v_j_770_ = lean_usize_to_nat(v___x_769_);
v___x_771_ = lean_array_get_borrowed(v___x_767_, v_es_766_, v_j_770_);
lean_dec(v_j_770_);
switch(lean_obj_tag(v___x_771_))
{
case 0:
{
lean_object* v_key_772_; uint8_t v___x_773_; 
v_key_772_ = lean_ctor_get(v___x_771_, 0);
v___x_773_ = l_Lean_instBEqMVarId_beq(v_x_765_, v_key_772_);
return v___x_773_;
}
case 1:
{
lean_object* v_node_774_; size_t v___x_775_; size_t v___x_776_; 
v_node_774_ = lean_ctor_get(v___x_771_, 0);
v___x_775_ = ((size_t)5ULL);
v___x_776_ = lean_usize_shift_right(v_x_764_, v___x_775_);
v_x_763_ = v_node_774_;
v_x_764_ = v___x_776_;
goto _start;
}
default: 
{
uint8_t v___x_778_; 
v___x_778_ = 0;
return v___x_778_;
}
}
}
else
{
lean_object* v_ks_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_ks_779_ = lean_ctor_get(v_x_763_, 0);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_779_, v___x_780_, v_x_765_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
size_t v_x_9678__boxed_785_; uint8_t v_res_786_; lean_object* v_r_787_; 
v_x_9678__boxed_785_ = lean_unbox_usize(v_x_783_);
lean_dec(v_x_783_);
v_res_786_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_782_, v_x_9678__boxed_785_, v_x_784_);
lean_dec(v_x_784_);
lean_dec_ref(v_x_782_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
uint64_t v___x_790_; size_t v___x_791_; uint8_t v___x_792_; 
v___x_790_ = l_Lean_instHashableMVarId_hash(v_x_789_);
v___x_791_ = lean_uint64_to_usize(v___x_790_);
v___x_792_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_788_, v___x_791_, v_x_789_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg___boxed(lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_793_, v_x_794_);
lean_dec(v_x_794_);
lean_dec_ref(v_x_793_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(lean_object* v_mvarId_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; lean_object* v_mctx_801_; lean_object* v_eAssignment_802_; uint8_t v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_800_ = lean_st_ref_get(v___y_798_);
v_mctx_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc_ref(v_mctx_801_);
lean_dec(v___x_800_);
v_eAssignment_802_ = lean_ctor_get(v_mctx_801_, 8);
lean_inc_ref(v_eAssignment_802_);
lean_dec_ref(v_mctx_801_);
v___x_803_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_eAssignment_802_, v_mvarId_797_);
lean_dec_ref(v_eAssignment_802_);
v___x_804_ = lean_box(v___x_803_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg___boxed(lean_object* v_mvarId_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec(v_mvarId_806_);
return v_res_809_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__3));
v___x_819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__2));
v___x_820_ = l_Lean_mkConst(v___x_819_, v___x_818_);
return v___x_820_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = lean_box(0);
v___x_827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__7));
v___x_828_ = l_Lean_mkConst(v___x_827_, v___x_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; lean_object* v_mvarId_841_; lean_object* v___x_842_; lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_896_; 
v___x_840_ = lean_st_ref_get(v_a_829_);
v_mvarId_841_ = lean_ctor_get(v___x_840_, 1);
lean_inc(v_mvarId_841_);
lean_dec(v___x_840_);
v___x_842_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_841_, v_a_836_);
lean_dec(v_mvarId_841_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_896_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_896_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_896_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
uint8_t v___x_847_; 
v___x_847_ = lean_unbox(v_a_843_);
lean_dec(v_a_843_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_del_object(v___x_845_);
v___x_848_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_833_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_850_ = l_Lean_Meta_Grind_mkEqFalseProof(v_a_849_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_833_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_833_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__8);
v___x_858_ = l_Lean_mkApp4(v___x_856_, v_a_853_, v_a_855_, v_a_851_, v___x_857_);
v___x_859_ = l_Lean_Meta_Grind_closeGoal(v___x_858_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
return v___x_859_;
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_a_853_);
lean_dec(v_a_851_);
v_a_860_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_854_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_854_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_a_851_);
v_a_868_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_852_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_852_);
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
v_a_876_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_850_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_850_);
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
v_a_884_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_848_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_848_);
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
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_892_);
v___x_894_ = v___x_845_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___boxed(lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec(v_a_897_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(lean_object* v_mvarId_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___redArg(v_mvarId_909_, v___y_917_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0___boxed(lean_object* v_mvarId_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0(v_mvarId_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec(v___y_923_);
lean_dec(v_mvarId_922_);
return v_res_934_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(lean_object* v_00_u03b2_935_, lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
uint8_t v___x_938_; 
v___x_938_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___redArg(v_x_936_, v_x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0___boxed(lean_object* v_00_u03b2_939_, lean_object* v_x_940_, lean_object* v_x_941_){
_start:
{
uint8_t v_res_942_; lean_object* v_r_943_; 
v_res_942_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0(v_00_u03b2_939_, v_x_940_, v_x_941_);
lean_dec(v_x_941_);
lean_dec_ref(v_x_940_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_944_, lean_object* v_x_945_, size_t v_x_946_, lean_object* v_x_947_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_945_, v_x_946_, v_x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_){
_start:
{
size_t v_x_9961__boxed_953_; uint8_t v_res_954_; lean_object* v_r_955_; 
v_x_9961__boxed_953_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_res_954_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_949_, v_x_950_, v_x_9961__boxed_953_, v_x_952_);
lean_dec(v_x_952_);
lean_dec_ref(v_x_950_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_956_, lean_object* v_keys_957_, lean_object* v_vals_958_, lean_object* v_heq_959_, lean_object* v_i_960_, lean_object* v_k_961_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_957_, v_i_960_, v_k_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_963_, lean_object* v_keys_964_, lean_object* v_vals_965_, lean_object* v_heq_966_, lean_object* v_i_967_, lean_object* v_k_968_){
_start:
{
uint8_t v_res_969_; lean_object* v_r_970_; 
v_res_969_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_963_, v_keys_964_, v_vals_965_, v_heq_966_, v_i_967_, v_k_968_);
lean_dec(v_k_968_);
lean_dec_ref(v_vals_965_);
lean_dec_ref(v_keys_964_);
v_r_970_ = lean_box(v_res_969_);
return v_r_970_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_box(0);
v___x_975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__1));
v___x_976_ = l_Lean_mkConst(v___x_975_, v___x_974_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(lean_object* v_lhs_977_, lean_object* v_rhs_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; 
lean_inc_ref(v_rhs_978_);
lean_inc_ref(v_lhs_977_);
v___x_990_ = l_Lean_Meta_mkEq(v_lhs_977_, v_rhs_978_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
lean_inc(v_a_988_);
lean_inc_ref(v_a_987_);
lean_inc(v_a_986_);
lean_inc_ref(v_a_985_);
lean_inc(v_a_984_);
lean_inc_ref(v_a_983_);
lean_inc(v_a_982_);
lean_inc_ref(v_a_981_);
lean_inc(v_a_980_);
lean_inc(v_a_979_);
v___x_992_ = lean_grind_mk_eq_proof(v_lhs_977_, v_rhs_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
lean_inc(v_a_991_);
v___x_994_ = l_Lean_Meta_mkDecide(v_a_991_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v___x_996_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_983_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___closed__2);
v___x_999_ = l_Lean_Expr_appArg_x21(v_a_995_);
lean_dec(v_a_995_);
v___x_1000_ = l_Lean_eagerReflBoolFalse;
lean_inc(v_a_991_);
v___x_1001_ = l_Lean_mkApp3(v___x_998_, v_a_991_, v___x_999_, v___x_1000_);
v___x_1002_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse___closed__4);
v___x_1003_ = l_Lean_mkApp4(v___x_1002_, v_a_991_, v_a_997_, v___x_1001_, v_a_993_);
v___x_1004_ = l_Lean_Meta_Grind_closeGoal(v___x_1003_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_1004_;
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec(v_a_995_);
lean_dec(v_a_993_);
lean_dec(v_a_991_);
v_a_1005_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_996_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_996_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v_a_993_);
lean_dec(v_a_991_);
v_a_1013_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_994_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_994_);
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
lean_dec(v_a_991_);
v_a_1021_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_992_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_992_);
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
lean_dec_ref(v_rhs_978_);
lean_dec_ref(v_lhs_977_);
v_a_1029_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_990_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_990_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq___boxed(lean_object* v_lhs_1037_, lean_object* v_rhs_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_lhs_1037_, v_rhs_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec(v_a_1039_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(lean_object* v___x_1051_, lean_object* v_as_x27_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
if (lean_obj_tag(v_as_x27_1052_) == 0)
{
lean_object* v___x_1065_; 
lean_dec(v___x_1051_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v_b_1053_);
return v___x_1065_;
}
else
{
lean_object* v_head_1066_; lean_object* v_tail_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_head_1066_ = lean_ctor_get(v_as_x27_1052_, 0);
v_tail_1067_ = lean_ctor_get(v_as_x27_1052_, 1);
v___x_1068_ = lean_st_ref_get(v___y_1054_);
lean_inc(v_head_1066_);
v___x_1069_ = l_Lean_Meta_Grind_Goal_getENode(v___x_1068_, v_head_1066_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_self_1071_; lean_object* v_next_1072_; lean_object* v_root_1073_; lean_object* v_congr_1074_; lean_object* v_target_x3f_1075_; lean_object* v_proof_x3f_1076_; uint8_t v_flipped_1077_; lean_object* v_size_1078_; uint8_t v_interpreted_1079_; uint8_t v_ctor_1080_; uint8_t v_hasLambdas_1081_; uint8_t v_heqProofs_1082_; lean_object* v_idx_1083_; lean_object* v_generation_1084_; lean_object* v_mt_1085_; lean_object* v_sTerms_1086_; uint8_t v_funCC_1087_; lean_object* v_ematchDiagSource_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1101_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v_self_1071_ = lean_ctor_get(v_a_1070_, 0);
v_next_1072_ = lean_ctor_get(v_a_1070_, 1);
v_root_1073_ = lean_ctor_get(v_a_1070_, 2);
v_congr_1074_ = lean_ctor_get(v_a_1070_, 3);
v_target_x3f_1075_ = lean_ctor_get(v_a_1070_, 4);
v_proof_x3f_1076_ = lean_ctor_get(v_a_1070_, 5);
v_flipped_1077_ = lean_ctor_get_uint8(v_a_1070_, sizeof(void*)*12);
v_size_1078_ = lean_ctor_get(v_a_1070_, 6);
v_interpreted_1079_ = lean_ctor_get_uint8(v_a_1070_, sizeof(void*)*12 + 1);
v_ctor_1080_ = lean_ctor_get_uint8(v_a_1070_, sizeof(void*)*12 + 2);
v_hasLambdas_1081_ = lean_ctor_get_uint8(v_a_1070_, sizeof(void*)*12 + 3);
v_heqProofs_1082_ = lean_ctor_get_uint8(v_a_1070_, sizeof(void*)*12 + 4);
v_idx_1083_ = lean_ctor_get(v_a_1070_, 7);
v_generation_1084_ = lean_ctor_get(v_a_1070_, 8);
v_mt_1085_ = lean_ctor_get(v_a_1070_, 9);
v_sTerms_1086_ = lean_ctor_get(v_a_1070_, 10);
v_funCC_1087_ = lean_ctor_get_uint8(v_a_1070_, sizeof(void*)*12 + 5);
v_ematchDiagSource_1088_ = lean_ctor_get(v_a_1070_, 11);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_a_1070_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1090_ = v_a_1070_;
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_ematchDiagSource_1088_);
lean_inc(v_sTerms_1086_);
lean_inc(v_mt_1085_);
lean_inc(v_generation_1084_);
lean_inc(v_idx_1083_);
lean_inc(v_size_1078_);
lean_inc(v_proof_x3f_1076_);
lean_inc(v_target_x3f_1075_);
lean_inc(v_congr_1074_);
lean_inc(v_root_1073_);
lean_inc(v_next_1072_);
lean_inc(v_self_1071_);
lean_dec(v_a_1070_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_nat_dec_lt(v_mt_1085_, v___x_1051_);
lean_dec(v_mt_1085_);
if (v___x_1093_ == 0)
{
lean_del_object(v___x_1090_);
lean_dec(v_ematchDiagSource_1088_);
lean_dec(v_sTerms_1086_);
lean_dec(v_generation_1084_);
lean_dec(v_idx_1083_);
lean_dec(v_size_1078_);
lean_dec(v_proof_x3f_1076_);
lean_dec(v_target_x3f_1075_);
lean_dec_ref(v_congr_1074_);
lean_dec_ref(v_root_1073_);
lean_dec_ref(v_next_1072_);
lean_dec_ref(v_self_1071_);
v_as_x27_1052_ = v_tail_1067_;
v_b_1053_ = v___x_1092_;
goto _start;
}
else
{
lean_object* v___x_1096_; 
lean_inc(v___x_1051_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 9, v___x_1051_);
v___x_1096_ = v___x_1090_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_self_1071_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_next_1072_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v_root_1073_);
lean_ctor_set(v_reuseFailAlloc_1100_, 3, v_congr_1074_);
lean_ctor_set(v_reuseFailAlloc_1100_, 4, v_target_x3f_1075_);
lean_ctor_set(v_reuseFailAlloc_1100_, 5, v_proof_x3f_1076_);
lean_ctor_set(v_reuseFailAlloc_1100_, 6, v_size_1078_);
lean_ctor_set(v_reuseFailAlloc_1100_, 7, v_idx_1083_);
lean_ctor_set(v_reuseFailAlloc_1100_, 8, v_generation_1084_);
lean_ctor_set(v_reuseFailAlloc_1100_, 9, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1100_, 10, v_sTerms_1086_);
lean_ctor_set(v_reuseFailAlloc_1100_, 11, v_ematchDiagSource_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1100_, sizeof(void*)*12, v_flipped_1077_);
lean_ctor_set_uint8(v_reuseFailAlloc_1100_, sizeof(void*)*12 + 1, v_interpreted_1079_);
lean_ctor_set_uint8(v_reuseFailAlloc_1100_, sizeof(void*)*12 + 2, v_ctor_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1100_, sizeof(void*)*12 + 3, v_hasLambdas_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1100_, sizeof(void*)*12 + 4, v_heqProofs_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1100_, sizeof(void*)*12 + 5, v_funCC_1087_);
v___x_1096_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; 
lean_inc(v_head_1066_);
v___x_1097_ = l_Lean_Meta_Grind_setENode___redArg(v_head_1066_, v___x_1096_, v___y_1054_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; 
lean_dec_ref_known(v___x_1097_, 1);
v___x_1098_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_head_1066_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_dec_ref_known(v___x_1098_, 1);
v_as_x27_1052_ = v_tail_1067_;
v_b_1053_ = v___x_1092_;
goto _start;
}
else
{
lean_dec(v___x_1051_);
return v___x_1098_;
}
}
else
{
lean_dec(v___x_1051_);
return v___x_1097_;
}
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v___x_1051_);
v_a_1102_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1069_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1069_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(lean_object* v_root_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_st_ref_get(v_a_1111_);
v___x_1123_ = l_Lean_Meta_Grind_getParents___redArg(v_root_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_toGoalState_1124_; lean_object* v_ematch_1125_; lean_object* v_a_1126_; lean_object* v_gmt_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_toGoalState_1124_ = lean_ctor_get(v___x_1122_, 0);
lean_inc_ref(v_toGoalState_1124_);
lean_dec(v___x_1122_);
v_ematch_1125_ = lean_ctor_get(v_toGoalState_1124_, 12);
lean_inc_ref(v_ematch_1125_);
lean_dec_ref(v_toGoalState_1124_);
v_a_1126_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1123_, 1);
v_gmt_1127_ = lean_ctor_get(v_ematch_1125_, 1);
lean_inc(v_gmt_1127_);
lean_dec_ref(v_ematch_1125_);
v___x_1128_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1126_);
lean_dec(v_a_1126_);
v___x_1129_ = lean_box(0);
v___x_1130_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v_gmt_1127_, v___x_1128_, v___x_1129_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v___x_1128_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v___x_1130_, 0);
lean_dec(v_unused_1138_);
v___x_1132_ = v___x_1130_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_dec(v___x_1130_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1129_);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1129_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
return v___x_1130_;
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec(v___x_1122_);
v_a_1139_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1123_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1123_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT___boxed(lean_object* v_root_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v_root_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_root_1147_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg___boxed(lean_object* v___x_1160_, lean_object* v_as_x27_1161_, lean_object* v_b_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1160_, v_as_x27_1161_, v_b_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec(v_as_x27_1161_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(lean_object* v___x_1175_, lean_object* v_as_1176_, lean_object* v_as_x27_1177_, lean_object* v_b_1178_, lean_object* v_a_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___redArg(v___x_1175_, v_as_x27_1177_, v_b_1178_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0___boxed(lean_object* v___x_1192_, lean_object* v_as_1193_, lean_object* v_as_x27_1194_, lean_object* v_b_1195_, lean_object* v_a_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT_spec__0(v___x_1192_, v_as_1193_, v_as_x27_1194_, v_b_1195_, v_a_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec(v_as_x27_1194_);
lean_dec(v_as_1193_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
if (lean_obj_tag(v_a_1209_) == 0)
{
lean_object* v___x_1211_; 
v___x_1211_ = l_List_reverse___redArg(v_a_1210_);
return v___x_1211_;
}
else
{
lean_object* v_head_1212_; lean_object* v_tail_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1222_; 
v_head_1212_ = lean_ctor_get(v_a_1209_, 0);
v_tail_1213_ = lean_ctor_get(v_a_1209_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_a_1209_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1215_ = v_a_1209_;
v_isShared_1216_ = v_isSharedCheck_1222_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_tail_1213_);
lean_inc(v_head_1212_);
lean_dec(v_a_1209_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1222_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = l_Lean_MessageData_ofExpr(v_head_1212_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v_a_1210_);
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_a_1210_);
v___x_1219_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
v_a_1209_ = v_tail_1213_;
v_a_1210_ = v___x_1219_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(lean_object* v_snd_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_fst_1226_, lean_object* v_lams_1227_, lean_object* v_____r_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_Meta_Grind_isEqv___redArg(v_snd_1223_, v_a_1224_, v___y_1229_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; uint8_t v___x_1289_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1289_ = lean_unbox(v_a_1288_);
lean_dec(v_a_1288_);
if (v___x_1289_ == 0)
{
v___y_1241_ = v___y_1229_;
v___y_1242_ = v___y_1230_;
v___y_1243_ = v___y_1231_;
v___y_1244_ = v___y_1232_;
v___y_1245_ = v___y_1233_;
v___y_1246_ = v___y_1234_;
v___y_1247_ = v___y_1235_;
v___y_1248_ = v___y_1236_;
v___y_1249_ = v___y_1237_;
v___y_1250_ = v___y_1238_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_inc(v_fst_1226_);
v___x_1290_ = l_Array_reverse___redArg(v_fst_1226_);
lean_inc(v_snd_1223_);
v___x_1291_ = l_Lean_Meta_Grind_propagateBetaEqs(v_lams_1227_, v_snd_1223_, v___x_1290_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_dec_ref_known(v___x_1291_, 1);
v___y_1241_ = v___y_1229_;
v___y_1242_ = v___y_1230_;
v___y_1243_ = v___y_1231_;
v___y_1244_ = v___y_1232_;
v___y_1245_ = v___y_1233_;
v___y_1246_ = v___y_1234_;
v___y_1247_ = v___y_1235_;
v___y_1248_ = v___y_1236_;
v___y_1249_ = v___y_1237_;
v___y_1250_ = v___y_1238_;
goto v___jp_1240_;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_fst_1226_);
lean_dec(v_snd_1223_);
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
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
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_fst_1226_);
lean_dec(v_snd_1223_);
v_a_1300_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1287_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1287_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
v___jp_1240_:
{
if (lean_obj_tag(v_snd_1223_) == 5)
{
lean_object* v_fn_1251_; lean_object* v_arg_1252_; lean_object* v___x_1253_; 
v_fn_1251_ = lean_ctor_get(v_snd_1223_, 0);
lean_inc_ref(v_fn_1251_);
v_arg_1252_ = lean_ctor_get(v_snd_1223_, 1);
lean_inc_ref(v_arg_1252_);
v___x_1253_ = l_Lean_Meta_Grind_getGeneration___redArg(v_a_1225_, v___y_1241_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1255_ = lean_box(0);
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc(v___y_1241_);
v___x_1256_ = lean_grind_internalize(v_snd_1223_, v_a_1254_, v___x_1255_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1266_; 
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1256_, 0);
lean_dec(v_unused_1267_);
v___x_1258_ = v___x_1256_;
v_isShared_1259_ = v_isSharedCheck_1266_;
goto v_resetjp_1257_;
}
else
{
lean_dec(v___x_1256_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1266_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1260_ = lean_array_push(v_fst_1226_, v_arg_1252_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v_fn_1251_);
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1262_);
v___x_1264_ = v___x_1258_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_arg_1252_);
lean_dec_ref(v_fn_1251_);
lean_dec(v_fst_1226_);
v_a_1268_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1256_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1256_);
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
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_arg_1252_);
lean_dec_ref_known(v_snd_1223_, 2);
lean_dec_ref(v_fn_1251_);
lean_dec(v_fst_1226_);
v_a_1276_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1253_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1253_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_fst_1226_);
lean_ctor_set(v___x_1284_, 1, v_snd_1223_);
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_snd_1308_ = _args[0];
lean_object* v_a_1309_ = _args[1];
lean_object* v_a_1310_ = _args[2];
lean_object* v_fst_1311_ = _args[3];
lean_object* v_lams_1312_ = _args[4];
lean_object* v_____r_1313_ = _args[5];
lean_object* v___y_1314_ = _args[6];
lean_object* v___y_1315_ = _args[7];
lean_object* v___y_1316_ = _args[8];
lean_object* v___y_1317_ = _args[9];
lean_object* v___y_1318_ = _args[10];
lean_object* v___y_1319_ = _args[11];
lean_object* v___y_1320_ = _args[12];
lean_object* v___y_1321_ = _args[13];
lean_object* v___y_1322_ = _args[14];
lean_object* v___y_1323_ = _args[15];
lean_object* v___y_1324_ = _args[16];
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1308_, v_a_1309_, v_a_1310_, v_fst_1311_, v_lams_1312_, v_____r_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v_lams_1312_);
lean_dec_ref(v_a_1310_);
lean_dec_ref(v_a_1309_);
return v_res_1325_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1332_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_1333_ = l_Lean_Name_append(v___x_1332_, v___x_1331_);
return v___x_1333_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__3));
v___x_1336_ = l_Lean_stringToMessageData(v___x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_lams_1339_, lean_object* v_a_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___y_1353_; lean_object* v_options_1373_; lean_object* v_fst_1374_; lean_object* v_snd_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1413_; 
v_options_1373_ = lean_ctor_get(v___y_1349_, 1);
v_fst_1374_ = lean_ctor_get(v_a_1340_, 0);
v_snd_1375_ = lean_ctor_get(v_a_1340_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_a_1340_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1377_ = v_a_1340_;
v_isShared_1378_ = v_isSharedCheck_1413_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_snd_1375_);
lean_inc(v_fst_1374_);
lean_dec(v_a_1340_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1413_;
goto v_resetjp_1376_;
}
v___jp_1352_:
{
if (lean_obj_tag(v___y_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1364_; 
v_a_1354_ = lean_ctor_get(v___y_1353_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___y_1353_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1356_ = v___y_1353_;
v_isShared_1357_ = v_isSharedCheck_1364_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___y_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1364_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
if (lean_obj_tag(v_a_1354_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; 
v_a_1358_ = lean_ctor_get(v_a_1354_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v_a_1354_, 1);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v_a_1358_);
v___x_1360_ = v___x_1356_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v_a_1362_; 
lean_del_object(v___x_1356_);
v_a_1362_ = lean_ctor_get(v_a_1354_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v_a_1354_, 1);
v_a_1340_ = v_a_1362_;
goto _start;
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_a_1365_ = lean_ctor_get(v___y_1353_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___y_1353_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___y_1353_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___y_1353_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
v_resetjp_1376_:
{
lean_object* v_toCold_1379_; uint8_t v_hasTrace_1380_; 
v_toCold_1379_ = lean_ctor_get(v___y_1349_, 0);
v_hasTrace_1380_ = lean_ctor_get_uint8(v_options_1373_, sizeof(void*)*1);
if (v_hasTrace_1380_ == 0)
{
lean_del_object(v___x_1377_);
goto v___jp_1381_;
}
else
{
lean_object* v_inheritedTraceOptions_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_inheritedTraceOptions_1384_ = lean_ctor_get(v_toCold_1379_, 4);
v___x_1385_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1386_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1387_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1384_, v_options_1373_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_del_object(v___x_1377_);
goto v___jp_1381_;
}
else
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_Meta_Grind_updateLastTag(v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_dec_ref_known(v___x_1388_, 1);
v___x_1389_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__4);
lean_inc(v_snd_1375_);
v___x_1390_ = l_Lean_MessageData_ofExpr(v_snd_1375_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 7);
lean_ctor_set(v___x_1377_, 1, v___x_1390_);
lean_ctor_set(v___x_1377_, 0, v___x_1389_);
v___x_1392_ = v___x_1377_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1385_, v___x_1392_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1395_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1375_, v_a_1338_, v_a_1337_, v_fst_1374_, v_lams_1339_, v_a_1394_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
v___y_1353_ = v___x_1395_;
goto v___jp_1352_;
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_snd_1375_);
lean_dec(v_fst_1374_);
v_a_1396_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1393_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1393_);
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
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_del_object(v___x_1377_);
lean_dec(v_snd_1375_);
lean_dec(v_fst_1374_);
v_a_1405_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1388_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1388_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
v___jp_1381_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___lam__0(v_snd_1375_, v_a_1338_, v_a_1337_, v_fst_1374_, v_lams_1339_, v___x_1382_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
v___y_1353_ = v___x_1383_;
goto v___jp_1352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___boxed(lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_lams_1416_, lean_object* v_a_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1414_, v_a_1415_, v_lams_1416_, v_a_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v_lams_1416_);
lean_dec_ref(v_a_1415_);
lean_dec_ref(v_a_1414_);
return v_res_1429_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__1));
v___x_1434_ = l_Lean_stringToMessageData(v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(lean_object* v_a_1435_, lean_object* v_lams_1436_, lean_object* v_as_x27_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
if (lean_obj_tag(v_as_x27_1437_) == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v_b_1438_);
return v___x_1450_;
}
else
{
lean_object* v_toCold_1451_; lean_object* v_options_1452_; lean_object* v_head_1453_; lean_object* v_tail_1454_; lean_object* v_inheritedTraceOptions_1455_; uint8_t v_hasTrace_1456_; lean_object* v___x_1457_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___x_1481_; uint8_t v_a_1483_; 
v_toCold_1451_ = lean_ctor_get(v___y_1447_, 0);
v_options_1452_ = lean_ctor_get(v___y_1447_, 1);
v_head_1453_ = lean_ctor_get(v_as_x27_1437_, 0);
v_tail_1454_ = lean_ctor_get(v_as_x27_1437_, 1);
v_inheritedTraceOptions_1455_ = lean_ctor_get(v_toCold_1451_, 4);
v_hasTrace_1456_ = lean_ctor_get_uint8(v_options_1452_, sizeof(void*)*1);
v___x_1457_ = lean_box(0);
v___x_1481_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
if (v_hasTrace_1456_ == 0)
{
v_a_1483_ = v_hasTrace_1456_;
goto v___jp_1482_;
}
else
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1491_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1455_, v_options_1452_, v___x_1490_);
v_a_1483_ = v___x_1491_;
goto v___jp_1482_;
}
v___jp_1458_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_inc(v_head_1453_);
lean_inc_ref(v___y_1459_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___y_1459_);
lean_ctor_set(v___x_1470_, 1, v_head_1453_);
v___x_1471_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1453_, v_a_1435_, v_lams_1436_, v___x_1470_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_dec_ref_known(v___x_1471_, 1);
v_as_x27_1437_ = v_tail_1454_;
v_b_1438_ = v___x_1457_;
goto _start;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1471_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1471_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
v___jp_1482_:
{
lean_object* v___x_1484_; 
v___x_1484_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1483_ == 0)
{
v___y_1459_ = v___x_1484_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
v___y_1466_ = v___y_1445_;
v___y_1467_ = v___y_1446_;
v___y_1468_ = v___y_1447_;
v___y_1469_ = v___y_1448_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_Meta_Grind_updateLastTag(v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref_known(v___x_1485_, 1);
v___x_1486_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1453_);
v___x_1487_ = l_Lean_MessageData_ofExpr(v_head_1453_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1481_, v___x_1488_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_dec_ref_known(v___x_1489_, 1);
v___y_1459_ = v___x_1484_;
v___y_1460_ = v___y_1439_;
v___y_1461_ = v___y_1440_;
v___y_1462_ = v___y_1441_;
v___y_1463_ = v___y_1442_;
v___y_1464_ = v___y_1443_;
v___y_1465_ = v___y_1444_;
v___y_1466_ = v___y_1445_;
v___y_1467_ = v___y_1446_;
v___y_1468_ = v___y_1447_;
v___y_1469_ = v___y_1448_;
goto v___jp_1458_;
}
else
{
return v___x_1489_;
}
}
else
{
return v___x_1485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___boxed(lean_object* v_a_1492_, lean_object* v_lams_1493_, lean_object* v_as_x27_1494_, lean_object* v_b_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1492_, v_lams_1493_, v_as_x27_1494_, v_b_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec(v_as_x27_1494_);
lean_dec_ref(v_lams_1493_);
lean_dec_ref(v_a_1492_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(lean_object* v_a_1508_, lean_object* v_lams_1509_, lean_object* v_as_1510_, lean_object* v_as_x27_1511_, lean_object* v_b_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
if (lean_obj_tag(v_as_x27_1511_) == 0)
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_b_1512_);
return v___x_1524_;
}
else
{
lean_object* v_toCold_1525_; lean_object* v_options_1526_; lean_object* v_head_1527_; lean_object* v_tail_1528_; lean_object* v_inheritedTraceOptions_1529_; uint8_t v_hasTrace_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; uint8_t v_a_1557_; 
v_toCold_1525_ = lean_ctor_get(v___y_1521_, 0);
v_options_1526_ = lean_ctor_get(v___y_1521_, 1);
v_head_1527_ = lean_ctor_get(v_as_x27_1511_, 0);
v_tail_1528_ = lean_ctor_get(v_as_x27_1511_, 1);
v_inheritedTraceOptions_1529_ = lean_ctor_get(v_toCold_1525_, 4);
v_hasTrace_1530_ = lean_ctor_get_uint8(v_options_1526_, sizeof(void*)*1);
v___x_1531_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1532_ = lean_box(0);
if (v_hasTrace_1530_ == 0)
{
v_a_1557_ = v_hasTrace_1530_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1565_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1529_, v_options_1526_, v___x_1564_);
v_a_1557_ = v___x_1565_;
goto v___jp_1556_;
}
v___jp_1533_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_inc(v_head_1527_);
lean_inc_ref(v___y_1534_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___y_1534_);
lean_ctor_set(v___x_1545_, 1, v_head_1527_);
v___x_1546_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_head_1527_, v_a_1508_, v_lams_1509_, v___x_1545_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1547_; 
lean_dec_ref_known(v___x_1546_, 1);
v___x_1547_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1508_, v_lams_1509_, v_tail_1528_, v___x_1532_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1547_;
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v_a_1548_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1546_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1546_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
v___jp_1556_:
{
lean_object* v___x_1558_; 
v___x_1558_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
if (v_a_1557_ == 0)
{
v___y_1534_ = v___x_1558_;
v___y_1535_ = v___y_1513_;
v___y_1536_ = v___y_1514_;
v___y_1537_ = v___y_1515_;
v___y_1538_ = v___y_1516_;
v___y_1539_ = v___y_1517_;
v___y_1540_ = v___y_1518_;
v___y_1541_ = v___y_1519_;
v___y_1542_ = v___y_1520_;
v___y_1543_ = v___y_1521_;
v___y_1544_ = v___y_1522_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Meta_Grind_updateLastTag(v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec_ref_known(v___x_1559_, 1);
v___x_1560_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__2);
lean_inc(v_head_1527_);
v___x_1561_ = l_Lean_MessageData_ofExpr(v_head_1527_);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1531_, v___x_1562_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_dec_ref_known(v___x_1563_, 1);
v___y_1534_ = v___x_1558_;
v___y_1535_ = v___y_1513_;
v___y_1536_ = v___y_1514_;
v___y_1537_ = v___y_1515_;
v___y_1538_ = v___y_1516_;
v___y_1539_ = v___y_1517_;
v___y_1540_ = v___y_1518_;
v___y_1541_ = v___y_1519_;
v___y_1542_ = v___y_1520_;
v___y_1543_ = v___y_1521_;
v___y_1544_ = v___y_1522_;
goto v___jp_1533_;
}
else
{
return v___x_1563_;
}
}
else
{
return v___x_1559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg___boxed(lean_object* v_a_1566_, lean_object* v_lams_1567_, lean_object* v_as_1568_, lean_object* v_as_x27_1569_, lean_object* v_b_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1566_, v_lams_1567_, v_as_1568_, v_as_x27_1569_, v_b_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec(v_as_x27_1569_);
lean_dec(v_as_1568_);
lean_dec_ref(v_lams_1567_);
lean_dec_ref(v_a_1566_);
return v_res_1582_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__0));
v___x_1585_ = l_Lean_stringToMessageData(v___x_1584_);
return v___x_1585_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4___closed__2));
v___x_1588_ = l_Lean_stringToMessageData(v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(lean_object* v_a_1589_, lean_object* v_lams_1590_, lean_object* v_as_1591_, size_t v_sz_1592_, size_t v_i_1593_, lean_object* v_b_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
uint8_t v___x_1606_; 
v___x_1606_ = lean_usize_dec_lt(v_i_1593_, v_sz_1592_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1607_, 0, v_b_1594_);
return v___x_1607_;
}
else
{
lean_object* v_toCold_1608_; lean_object* v_options_1609_; lean_object* v_inheritedTraceOptions_1610_; uint8_t v_hasTrace_1611_; lean_object* v___x_1612_; lean_object* v_a_1613_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; 
v_toCold_1608_ = lean_ctor_get(v___y_1603_, 0);
v_options_1609_ = lean_ctor_get(v___y_1603_, 1);
v_inheritedTraceOptions_1610_ = lean_ctor_get(v_toCold_1608_, 4);
v_hasTrace_1611_ = lean_ctor_get_uint8(v_options_1609_, sizeof(void*)*1);
v___x_1612_ = lean_box(0);
v_a_1613_ = lean_array_uget_borrowed(v_as_1591_, v_i_1593_);
if (v_hasTrace_1611_ == 0)
{
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
v___y_1622_ = v___y_1602_;
v___y_1623_ = v___y_1603_;
v___y_1624_ = v___y_1604_;
goto v___jp_1614_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1640_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1641_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1642_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1610_, v_options_1609_, v___x_1641_);
if (v___x_1642_ == 0)
{
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
v___y_1622_ = v___y_1602_;
v___y_1623_ = v___y_1603_;
v___y_1624_ = v___y_1604_;
goto v___jp_1614_;
}
else
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Meta_Grind_updateLastTag(v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1644_; 
lean_dec_ref_known(v___x_1643_, 1);
v___x_1644_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1613_, v___y_1595_);
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
v___x_1656_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1640_, v___x_1655_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_dec_ref_known(v___x_1656_, 1);
v___y_1615_ = v___y_1595_;
v___y_1616_ = v___y_1596_;
v___y_1617_ = v___y_1597_;
v___y_1618_ = v___y_1598_;
v___y_1619_ = v___y_1599_;
v___y_1620_ = v___y_1600_;
v___y_1621_ = v___y_1601_;
v___y_1622_ = v___y_1602_;
v___y_1623_ = v___y_1603_;
v___y_1624_ = v___y_1604_;
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
v___x_1628_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1589_, v_lams_1590_, v___x_1627_, v___x_1627_, v___x_1612_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___x_1627_);
if (lean_obj_tag(v___x_1628_) == 0)
{
size_t v___x_1629_; size_t v___x_1630_; 
lean_dec_ref_known(v___x_1628_, 1);
v___x_1629_ = ((size_t)1ULL);
v___x_1630_ = lean_usize_add(v_i_1593_, v___x_1629_);
v_i_1593_ = v___x_1630_;
v_b_1594_ = v___x_1612_;
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
lean_object* v_toCold_1704_; lean_object* v_options_1705_; lean_object* v_inheritedTraceOptions_1706_; uint8_t v_hasTrace_1707_; lean_object* v___x_1708_; lean_object* v_a_1709_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; 
v_toCold_1704_ = lean_ctor_get(v___y_1699_, 0);
v_options_1705_ = lean_ctor_get(v___y_1699_, 1);
v_inheritedTraceOptions_1706_ = lean_ctor_get(v_toCold_1704_, 4);
v_hasTrace_1707_ = lean_ctor_get_uint8(v_options_1705_, sizeof(void*)*1);
v___x_1708_ = lean_box(0);
v_a_1709_ = lean_array_uget_borrowed(v_as_1687_, v_i_1689_);
if (v_hasTrace_1707_ == 0)
{
v___y_1711_ = v___y_1691_;
v___y_1712_ = v___y_1692_;
v___y_1713_ = v___y_1693_;
v___y_1714_ = v___y_1694_;
v___y_1715_ = v___y_1695_;
v___y_1716_ = v___y_1696_;
v___y_1717_ = v___y_1697_;
v___y_1718_ = v___y_1698_;
v___y_1719_ = v___y_1699_;
v___y_1720_ = v___y_1700_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1736_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1737_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1738_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1706_, v_options_1705_, v___x_1737_);
if (v___x_1738_ == 0)
{
v___y_1711_ = v___y_1691_;
v___y_1712_ = v___y_1692_;
v___y_1713_ = v___y_1693_;
v___y_1714_ = v___y_1694_;
v___y_1715_ = v___y_1695_;
v___y_1716_ = v___y_1696_;
v___y_1717_ = v___y_1697_;
v___y_1718_ = v___y_1698_;
v___y_1719_ = v___y_1699_;
v___y_1720_ = v___y_1700_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Meta_Grind_updateLastTag(v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref_known(v___x_1739_, 1);
v___x_1740_ = l_Lean_Meta_Grind_getParents___redArg(v_a_1709_, v___y_1691_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
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
v___x_1752_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1736_, v___x_1751_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_dec_ref_known(v___x_1752_, 1);
v___y_1711_ = v___y_1691_;
v___y_1712_ = v___y_1692_;
v___y_1713_ = v___y_1693_;
v___y_1714_ = v___y_1694_;
v___y_1715_ = v___y_1695_;
v___y_1716_ = v___y_1696_;
v___y_1717_ = v___y_1697_;
v___y_1718_ = v___y_1698_;
v___y_1719_ = v___y_1699_;
v___y_1720_ = v___y_1700_;
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
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_1722_);
lean_dec(v_a_1722_);
v___x_1724_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1685_, v_lams_1686_, v___x_1723_, v___x_1723_, v___x_1708_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___x_1723_);
if (lean_obj_tag(v___x_1724_) == 0)
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref_known(v___x_1724_, 1);
v___x_1725_ = ((size_t)1ULL);
v___x_1726_ = lean_usize_add(v_i_1689_, v___x_1725_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_propagateBeta_spec__3_spec__4(v_a_1685_, v_lams_1686_, v_as_1687_, v_sz_1688_, v___x_1726_, v___x_1708_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
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
lean_dec_ref_known(v___x_1808_, 1);
v_options_1833_ = lean_ctor_get(v_a_1797_, 1);
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
lean_object* v_toCold_1835_; lean_object* v_inheritedTraceOptions_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_toCold_1835_ = lean_ctor_get(v_a_1797_, 0);
v_inheritedTraceOptions_1836_ = lean_ctor_get(v_toCold_1835_, 4);
v___x_1837_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__1));
v___x_1838_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg___closed__2);
v___x_1839_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1836_, v_options_1833_, v___x_1838_);
if (v___x_1839_ == 0)
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
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_Meta_Grind_updateLastTag(v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref_known(v___x_1840_, 1);
v___x_1841_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__1, &l_Lean_Meta_Grind_propagateBeta___closed__1_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__1);
lean_inc_ref(v_fns_1788_);
v___x_1842_ = lean_array_to_list(v_fns_1788_);
v___x_1843_ = lean_box(0);
v___x_1844_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1842_, v___x_1843_);
v___x_1845_ = l_Lean_MessageData_ofList(v___x_1844_);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1841_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = lean_obj_once(&l_Lean_Meta_Grind_propagateBeta___closed__3, &l_Lean_Meta_Grind_propagateBeta___closed__3_once, _init_l_Lean_Meta_Grind_propagateBeta___closed__3);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
lean_inc_ref(v_lams_1787_);
v___x_1849_ = lean_array_to_list(v_lams_1787_);
v___x_1850_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_propagateBeta_spec__2(v___x_1849_, v___x_1843_);
v___x_1851_ = l_Lean_MessageData_ofList(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1848_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_1837_, v___x_1852_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_dec_ref_known(v___x_1853_, 1);
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
return v___x_1853_;
}
}
else
{
lean_dec(v_a_1809_);
lean_dec_ref(v_fns_1788_);
lean_dec_ref(v_lams_1787_);
return v___x_1840_;
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
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v_fns_1788_);
lean_dec_ref(v_lams_1787_);
v_a_1854_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1808_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1808_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec_ref(v_fns_1788_);
lean_dec_ref(v_lams_1787_);
v___x_1862_ = lean_box(0);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBeta___boxed(lean_object* v_lams_1864_, lean_object* v_fns_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Meta_Grind_propagateBeta(v_lams_1864_, v_fns_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec(v_a_1866_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_lams_1880_, lean_object* v_inst_1881_, lean_object* v_a_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___redArg(v_a_1878_, v_a_1879_, v_lams_1880_, v_a_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0___boxed(lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_lams_1897_, lean_object* v_inst_1898_, lean_object* v_a_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_Grind_propagateBeta_spec__0(v_a_1895_, v_a_1896_, v_lams_1897_, v_inst_1898_, v_a_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v_lams_1897_);
lean_dec_ref(v_a_1896_);
lean_dec_ref(v_a_1895_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(lean_object* v_a_1912_, lean_object* v_lams_1913_, lean_object* v_as_1914_, lean_object* v_as_x27_1915_, lean_object* v_b_1916_, lean_object* v_a_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___redArg(v_a_1912_, v_lams_1913_, v_as_1914_, v_as_x27_1915_, v_b_1916_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1___boxed(lean_object** _args){
lean_object* v_a_1930_ = _args[0];
lean_object* v_lams_1931_ = _args[1];
lean_object* v_as_1932_ = _args[2];
lean_object* v_as_x27_1933_ = _args[3];
lean_object* v_b_1934_ = _args[4];
lean_object* v_a_1935_ = _args[5];
lean_object* v___y_1936_ = _args[6];
lean_object* v___y_1937_ = _args[7];
lean_object* v___y_1938_ = _args[8];
lean_object* v___y_1939_ = _args[9];
lean_object* v___y_1940_ = _args[10];
lean_object* v___y_1941_ = _args[11];
lean_object* v___y_1942_ = _args[12];
lean_object* v___y_1943_ = _args[13];
lean_object* v___y_1944_ = _args[14];
lean_object* v___y_1945_ = _args[15];
lean_object* v___y_1946_ = _args[16];
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1(v_a_1930_, v_lams_1931_, v_as_1932_, v_as_x27_1933_, v_b_1934_, v_a_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec(v_as_x27_1933_);
lean_dec(v_as_1932_);
lean_dec_ref(v_lams_1931_);
lean_dec_ref(v_a_1930_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(lean_object* v_a_1948_, lean_object* v_lams_1949_, lean_object* v_as_1950_, lean_object* v_as_x27_1951_, lean_object* v_b_1952_, lean_object* v_a_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg(v_a_1948_, v_lams_1949_, v_as_x27_1951_, v_b_1952_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___boxed(lean_object** _args){
lean_object* v_a_1966_ = _args[0];
lean_object* v_lams_1967_ = _args[1];
lean_object* v_as_1968_ = _args[2];
lean_object* v_as_x27_1969_ = _args[3];
lean_object* v_b_1970_ = _args[4];
lean_object* v_a_1971_ = _args[5];
lean_object* v___y_1972_ = _args[6];
lean_object* v___y_1973_ = _args[7];
lean_object* v___y_1974_ = _args[8];
lean_object* v___y_1975_ = _args[9];
lean_object* v___y_1976_ = _args[10];
lean_object* v___y_1977_ = _args[11];
lean_object* v___y_1978_ = _args[12];
lean_object* v___y_1979_ = _args[13];
lean_object* v___y_1980_ = _args[14];
lean_object* v___y_1981_ = _args[15];
lean_object* v___y_1982_ = _args[16];
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1(v_a_1966_, v_lams_1967_, v_as_1968_, v_as_x27_1969_, v_b_1970_, v_a_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec(v_as_x27_1969_);
lean_dec(v_as_1968_);
lean_dec_ref(v_lams_1967_);
lean_dec_ref(v_a_1966_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(lean_object* v_d_1987_, lean_object* v_as_1988_, size_t v_sz_1989_, size_t v_i_1990_, lean_object* v_b_1991_){
_start:
{
lean_object* v_a_1993_; uint8_t v___x_1997_; 
v___x_1997_ = lean_usize_dec_lt(v_i_1990_, v_sz_1989_);
if (v___x_1997_ == 0)
{
lean_inc_ref(v_b_1991_);
return v_b_1991_;
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v_a_2000_; 
v___x_1998_ = lean_box(0);
v___x_1999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_a_2000_ = lean_array_uget_borrowed(v_as_1988_, v_i_1990_);
if (lean_obj_tag(v_a_2000_) == 6)
{
lean_object* v_binderType_2001_; size_t v___x_2002_; size_t v___x_2003_; uint8_t v___x_2004_; 
v_binderType_2001_ = lean_ctor_get(v_a_2000_, 1);
v___x_2002_ = lean_ptr_addr(v_d_1987_);
v___x_2003_ = lean_ptr_addr(v_binderType_2001_);
v___x_2004_ = lean_usize_dec_eq(v___x_2002_, v___x_2003_);
if (v___x_2004_ == 0)
{
v_a_1993_ = v___x_1999_;
goto v___jp_1992_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_inc_ref(v_a_2000_);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_a_2000_);
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v___x_1998_);
return v___x_2007_;
}
}
else
{
v_a_1993_ = v___x_1999_;
goto v___jp_1992_;
}
}
v___jp_1992_:
{
size_t v___x_1994_; size_t v___x_1995_; 
v___x_1994_ = ((size_t)1ULL);
v___x_1995_ = lean_usize_add(v_i_1990_, v___x_1994_);
v_i_1990_ = v___x_1995_;
v_b_1991_ = v_a_1993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_2008_, lean_object* v_as_2009_, lean_object* v_sz_2010_, lean_object* v_i_2011_, lean_object* v_b_2012_){
_start:
{
size_t v_sz_boxed_2013_; size_t v_i_boxed_2014_; lean_object* v_res_2015_; 
v_sz_boxed_2013_ = lean_unbox_usize(v_sz_2010_);
lean_dec(v_sz_2010_);
v_i_boxed_2014_ = lean_unbox_usize(v_i_2011_);
lean_dec(v_i_2011_);
v_res_2015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2008_, v_as_2009_, v_sz_boxed_2013_, v_i_boxed_2014_, v_b_2012_);
lean_dec_ref(v_b_2012_);
lean_dec_ref(v_as_2009_);
lean_dec_ref(v_d_2008_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2016_, lean_object* v_d_2017_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; size_t v_sz_2020_; size_t v___x_2021_; lean_object* v___x_2022_; lean_object* v_fst_2023_; 
v___x_2018_ = lean_box(0);
v___x_2019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2020_ = lean_array_size(v_lams_2016_);
v___x_2021_ = ((size_t)0ULL);
v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2017_, v_lams_2016_, v_sz_2020_, v___x_2021_, v___x_2019_);
v_fst_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_fst_2023_);
lean_dec_ref(v___x_2022_);
if (lean_obj_tag(v_fst_2023_) == 0)
{
return v___x_2018_;
}
else
{
lean_object* v_val_2024_; 
v_val_2024_ = lean_ctor_get(v_fst_2023_, 0);
lean_inc(v_val_2024_);
lean_dec_ref_known(v_fst_2023_, 1);
return v_val_2024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2025_, lean_object* v_d_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2025_, v_d_2026_);
lean_dec_ref(v_d_2026_);
lean_dec_ref(v_lams_2025_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2038_, lean_object* v_lams_u2081_2039_, lean_object* v_as_2040_, size_t v_sz_2041_, size_t v_i_2042_, lean_object* v_b_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_a_2056_; uint8_t v___x_2060_; 
v___x_2060_ = lean_usize_dec_lt(v_i_2042_, v_sz_2041_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v_b_2043_);
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; lean_object* v_a_2063_; 
v___x_2062_ = lean_box(0);
v_a_2063_ = lean_array_uget_borrowed(v_as_2040_, v_i_2042_);
if (lean_obj_tag(v_a_2063_) == 6)
{
lean_object* v_binderType_2064_; lean_object* v_body_2065_; lean_object* v___x_2066_; 
v_binderType_2064_ = lean_ctor_get(v_a_2063_, 1);
v_body_2065_ = lean_ctor_get(v_a_2063_, 2);
lean_inc_ref(v_binderType_2064_);
v___x_2066_ = l_Lean_Meta_getLevel(v_binderType_2064_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2068_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2069_ = lean_box(0);
v___x_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_a_2067_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
lean_inc_ref(v___x_2070_);
v___x_2071_ = l_Lean_mkConst(v___x_2068_, v___x_2070_);
lean_inc_ref(v_binderType_2064_);
v___x_2072_ = l_Lean_Expr_app___override(v___x_2071_, v_binderType_2064_);
v___x_2073_ = lean_box(0);
v___x_2074_ = l_Lean_Meta_synthInstance_x3f(v___x_2072_, v___x_2073_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_2074_, 1);
if (lean_obj_tag(v_a_2075_) == 1)
{
lean_object* v_val_2076_; lean_object* v___x_2077_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; uint8_t v___x_2142_; 
v_val_2076_ = lean_ctor_get(v_a_2075_, 0);
lean_inc(v_val_2076_);
lean_dec_ref_known(v_a_2075_, 1);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2142_ = l_Lean_Expr_hasLooseBVars(v_body_2065_);
if (v___x_2142_ == 0)
{
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
v___y_2081_ = v___y_2046_;
v___y_2082_ = v___y_2047_;
v___y_2083_ = v___y_2048_;
v___y_2084_ = v___y_2049_;
v___y_2085_ = v___y_2050_;
v___y_2086_ = v___y_2051_;
v___y_2087_ = v___y_2052_;
v___y_2088_ = v___y_2053_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2070_);
v___x_2144_ = l_Lean_mkConst(v___x_2143_, v___x_2070_);
lean_inc_ref(v_binderType_2064_);
v___x_2145_ = l_Lean_Expr_app___override(v___x_2144_, v_binderType_2064_);
v___x_2146_ = l_Lean_Meta_synthInstance_x3f(v___x_2145_, v___x_2073_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
if (lean_obj_tag(v_a_2147_) == 0)
{
lean_dec(v_val_2076_);
lean_dec_ref_known(v___x_2070_, 2);
v_a_2056_ = v___x_2062_;
goto v___jp_2055_;
}
else
{
lean_dec_ref_known(v_a_2147_, 1);
if (v___x_2142_ == 0)
{
lean_dec(v_val_2076_);
lean_dec_ref_known(v___x_2070_, 2);
v_a_2056_ = v___x_2062_;
goto v___jp_2055_;
}
else
{
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
v___y_2081_ = v___y_2046_;
v___y_2082_ = v___y_2047_;
v___y_2083_ = v___y_2048_;
v___y_2084_ = v___y_2049_;
v___y_2085_ = v___y_2050_;
v___y_2086_ = v___y_2051_;
v___y_2087_ = v___y_2052_;
v___y_2088_ = v___y_2053_;
goto v___jp_2078_;
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_val_2076_);
lean_dec_ref_known(v___x_2070_, 2);
v_a_2148_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2146_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2146_);
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
v___jp_2078_:
{
lean_object* v___x_2089_; 
v___x_2089_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2038_, v_binderType_2064_);
if (lean_obj_tag(v___x_2089_) == 1)
{
lean_object* v_val_2090_; 
v_val_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v___x_2089_, 1);
if (lean_obj_tag(v_val_2090_) == 6)
{
lean_object* v_binderType_2091_; lean_object* v_body_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_binderType_2091_ = lean_ctor_get(v_val_2090_, 1);
lean_inc_ref(v_binderType_2091_);
v_body_2092_ = lean_ctor_get(v_val_2090_, 2);
lean_inc_ref(v_body_2092_);
lean_dec_ref_known(v_val_2090_, 3);
v___x_2093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2094_ = l_Lean_mkConst(v___x_2093_, v___x_2070_);
v___x_2095_ = l_Lean_mkAppB(v___x_2094_, v_binderType_2091_, v_val_2076_);
v___x_2096_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2095_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = lean_array_fget_borrowed(v_lams_u2081_2039_, v___x_2077_);
v___x_2099_ = lean_array_fget_borrowed(v_lams_u2082_2038_, v___x_2077_);
lean_inc(v___y_2088_);
lean_inc_ref(v___y_2087_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2080_);
lean_inc(v___y_2079_);
lean_inc(v___x_2099_);
lean_inc(v___x_2098_);
v___x_2100_ = lean_grind_mk_eq_proof(v___x_2098_, v___x_2099_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = lean_expr_instantiate1(v_body_2065_, v_a_2097_);
v___x_2103_ = lean_expr_instantiate1(v_body_2092_, v_a_2097_);
lean_dec_ref(v_body_2092_);
v___x_2104_ = l_Lean_Meta_mkCongrFun(v_a_2101_, v_a_2097_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = l_Lean_Meta_mkEq(v___x_2102_, v___x_2103_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = l_Lean_Meta_mkExpectedPropHint(v_a_2105_, v_a_2107_);
v___x_2109_ = l_Lean_Meta_Grind_pushNewFact(v___x_2108_, v___x_2077_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_dec_ref_known(v___x_2109_, 1);
v_a_2056_ = v___x_2062_;
goto v___jp_2055_;
}
else
{
return v___x_2109_;
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec(v_a_2105_);
v_a_2110_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2106_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2106_);
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
lean_dec_ref(v___x_2103_);
lean_dec_ref(v___x_2102_);
v_a_2118_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2104_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2104_);
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
lean_dec(v_a_2097_);
lean_dec_ref(v_body_2092_);
v_a_2126_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2100_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2100_);
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
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_body_2092_);
v_a_2134_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2096_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2096_);
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
else
{
lean_dec(v_val_2090_);
lean_dec(v_val_2076_);
lean_dec_ref_known(v___x_2070_, 2);
v_a_2056_ = v___x_2062_;
goto v___jp_2055_;
}
}
else
{
lean_dec(v___x_2089_);
lean_dec(v_val_2076_);
lean_dec_ref_known(v___x_2070_, 2);
v_a_2056_ = v___x_2062_;
goto v___jp_2055_;
}
}
}
else
{
lean_dec(v_a_2075_);
lean_dec_ref_known(v___x_2070_, 2);
v_a_2056_ = v___x_2062_;
goto v___jp_2055_;
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref_known(v___x_2070_, 2);
v_a_2156_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2074_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2074_);
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
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
v_a_2164_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2066_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2066_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
v_a_2056_ = v___x_2062_;
goto v___jp_2055_;
}
}
v___jp_2055_:
{
size_t v___x_2057_; size_t v___x_2058_; 
v___x_2057_ = ((size_t)1ULL);
v___x_2058_ = lean_usize_add(v_i_2042_, v___x_2057_);
v_i_2042_ = v___x_2058_;
v_b_2043_ = v_a_2056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2172_ = _args[0];
lean_object* v_lams_u2081_2173_ = _args[1];
lean_object* v_as_2174_ = _args[2];
lean_object* v_sz_2175_ = _args[3];
lean_object* v_i_2176_ = _args[4];
lean_object* v_b_2177_ = _args[5];
lean_object* v___y_2178_ = _args[6];
lean_object* v___y_2179_ = _args[7];
lean_object* v___y_2180_ = _args[8];
lean_object* v___y_2181_ = _args[9];
lean_object* v___y_2182_ = _args[10];
lean_object* v___y_2183_ = _args[11];
lean_object* v___y_2184_ = _args[12];
lean_object* v___y_2185_ = _args[13];
lean_object* v___y_2186_ = _args[14];
lean_object* v___y_2187_ = _args[15];
lean_object* v___y_2188_ = _args[16];
_start:
{
size_t v_sz_boxed_2189_; size_t v_i_boxed_2190_; lean_object* v_res_2191_; 
v_sz_boxed_2189_ = lean_unbox_usize(v_sz_2175_);
lean_dec(v_sz_2175_);
v_i_boxed_2190_ = lean_unbox_usize(v_i_2176_);
lean_dec(v_i_2176_);
v_res_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2172_, v_lams_u2081_2173_, v_as_2174_, v_sz_boxed_2189_, v_i_boxed_2190_, v_b_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v_as_2174_);
lean_dec_ref(v_lams_u2081_2173_);
lean_dec_ref(v_lams_u2082_2172_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2192_, lean_object* v_lams_u2082_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2205_ = lean_array_get_size(v_lams_u2081_2192_);
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = lean_nat_dec_eq(v___x_2205_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2208_ = lean_array_get_size(v_lams_u2082_2193_);
v___x_2209_ = lean_nat_dec_eq(v___x_2208_, v___x_2206_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; size_t v_sz_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = lean_box(0);
v_sz_2211_ = lean_array_size(v_lams_u2081_2192_);
v___x_2212_ = ((size_t)0ULL);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2193_, v_lams_u2081_2192_, v_lams_u2081_2192_, v_sz_2211_, v___x_2212_, v___x_2210_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v___x_2213_, 0);
lean_dec(v_unused_2221_);
v___x_2215_ = v___x_2213_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_dec(v___x_2213_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2210_);
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2210_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
else
{
return v___x_2213_;
}
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2226_, lean_object* v_lams_u2082_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2226_, v_lams_u2082_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_lams_u2082_2227_);
lean_dec_ref(v_lams_u2081_2226_);
return v_res_2239_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2240_){
_start:
{
uint8_t v___x_2241_; 
v___x_2241_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2242_){
_start:
{
uint8_t v_res_2243_; lean_object* v_r_2244_; 
v_res_2243_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2242_);
lean_dec_ref(v_x_2242_);
v_r_2244_ = lean_box(v_res_2243_);
return v_r_2244_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2245_, lean_object* v_x_2246_){
_start:
{
uint8_t v___x_2247_; 
v___x_2247_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2248_, lean_object* v_x_2249_){
_start:
{
uint8_t v_res_2250_; lean_object* v_r_2251_; 
v_res_2250_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2248_, v_x_2249_);
lean_dec_ref(v_x_2249_);
v_r_2251_ = lean_box(v_res_2250_);
return v_r_2251_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2252_, lean_object* v_v_2253_, lean_object* v_i_2254_){
_start:
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = lean_array_get_size(v_xs_2252_);
v___x_2256_ = lean_nat_dec_lt(v_i_2254_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; 
lean_dec(v_i_2254_);
v___x_2257_ = lean_box(0);
return v___x_2257_;
}
else
{
lean_object* v___x_2258_; size_t v___x_2259_; size_t v___x_2260_; uint8_t v___x_2261_; 
v___x_2258_ = lean_array_fget_borrowed(v_xs_2252_, v_i_2254_);
v___x_2259_ = lean_ptr_addr(v___x_2258_);
v___x_2260_ = lean_ptr_addr(v_v_2253_);
v___x_2261_ = lean_usize_dec_eq(v___x_2259_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = lean_nat_add(v_i_2254_, v___x_2262_);
lean_dec(v_i_2254_);
v_i_2254_ = v___x_2263_;
goto _start;
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_i_2254_);
return v___x_2265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2266_, lean_object* v_v_2267_, lean_object* v_i_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2266_, v_v_2267_, v_i_2268_);
lean_dec_ref(v_v_2267_);
lean_dec_ref(v_xs_2266_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2270_, lean_object* v_v_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_unsigned_to_nat(0u);
v___x_2273_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2270_, v_v_2271_, v___x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2274_, lean_object* v_v_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2274_, v_v_2275_);
lean_dec_ref(v_v_2275_);
lean_dec_ref(v_xs_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2277_, size_t v_x_2278_, lean_object* v_x_2279_){
_start:
{
if (lean_obj_tag(v_x_2277_) == 0)
{
lean_object* v_es_2280_; lean_object* v___x_2281_; size_t v___x_2282_; size_t v___x_2283_; lean_object* v_j_2284_; lean_object* v_entry_2285_; 
v_es_2280_ = lean_ctor_get(v_x_2277_, 0);
v___x_2281_ = lean_box(2);
v___x_2282_ = ((size_t)31ULL);
v___x_2283_ = lean_usize_land(v_x_2278_, v___x_2282_);
v_j_2284_ = lean_usize_to_nat(v___x_2283_);
v_entry_2285_ = lean_array_get(v___x_2281_, v_es_2280_, v_j_2284_);
switch(lean_obj_tag(v_entry_2285_))
{
case 0:
{
lean_object* v_key_2286_; size_t v___x_2287_; size_t v___x_2288_; uint8_t v___x_2289_; 
v_key_2286_ = lean_ctor_get(v_entry_2285_, 0);
lean_inc(v_key_2286_);
lean_dec_ref_known(v_entry_2285_, 2);
v___x_2287_ = lean_ptr_addr(v_x_2279_);
v___x_2288_ = lean_ptr_addr(v_key_2286_);
lean_dec(v_key_2286_);
v___x_2289_ = lean_usize_dec_eq(v___x_2287_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_dec(v_j_2284_);
return v_x_2277_;
}
else
{
lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2297_; 
lean_inc_ref(v_es_2280_);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_x_2277_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; 
v_unused_2298_ = lean_ctor_get(v_x_2277_, 0);
lean_dec(v_unused_2298_);
v___x_2291_ = v_x_2277_;
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
else
{
lean_dec(v_x_2277_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2297_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2293_ = lean_array_set(v_es_2280_, v_j_2284_, v___x_2281_);
lean_dec(v_j_2284_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2293_);
v___x_2295_ = v___x_2291_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
case 1:
{
lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2333_; 
lean_inc_ref(v_es_2280_);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_x_2277_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v_x_2277_, 0);
lean_dec(v_unused_2334_);
v___x_2300_ = v_x_2277_;
v_isShared_2301_ = v_isSharedCheck_2333_;
goto v_resetjp_2299_;
}
else
{
lean_dec(v_x_2277_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2333_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v_node_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2332_; 
v_node_2302_ = lean_ctor_get(v_entry_2285_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_entry_2285_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2304_ = v_entry_2285_;
v_isShared_2305_ = v_isSharedCheck_2332_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_node_2302_);
lean_dec(v_entry_2285_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2332_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
size_t v___x_2306_; lean_object* v_entries_2307_; size_t v___x_2308_; lean_object* v_newNode_2309_; lean_object* v___x_2310_; 
v___x_2306_ = ((size_t)5ULL);
v_entries_2307_ = lean_array_set(v_es_2280_, v_j_2284_, v___x_2281_);
v___x_2308_ = lean_usize_shift_right(v_x_2278_, v___x_2306_);
v_newNode_2309_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2302_, v___x_2308_, v_x_2279_);
lean_inc_ref(v_newNode_2309_);
v___x_2310_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2312_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v_newNode_2309_);
v___x_2312_ = v___x_2304_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_newNode_2309_);
v___x_2312_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2313_ = lean_array_set(v_entries_2307_, v_j_2284_, v___x_2312_);
lean_dec(v_j_2284_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2313_);
v___x_2315_ = v___x_2300_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
else
{
lean_object* v_val_2318_; lean_object* v_fst_2319_; lean_object* v_snd_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_newNode_2309_);
lean_del_object(v___x_2304_);
v_val_2318_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_val_2318_);
lean_dec_ref_known(v___x_2310_, 1);
v_fst_2319_ = lean_ctor_get(v_val_2318_, 0);
v_snd_2320_ = lean_ctor_get(v_val_2318_, 1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_val_2318_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2322_ = v_val_2318_;
v_isShared_2323_ = v_isSharedCheck_2331_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_snd_2320_);
lean_inc(v_fst_2319_);
lean_dec(v_val_2318_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2331_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fst_2319_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_snd_2320_);
v___x_2325_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2326_ = lean_array_set(v_entries_2307_, v_j_2284_, v___x_2325_);
lean_dec(v_j_2284_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2326_);
v___x_2328_ = v___x_2300_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_2284_);
return v_x_2277_;
}
}
}
else
{
lean_object* v_ks_2335_; lean_object* v_vs_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2350_; 
v_ks_2335_ = lean_ctor_get(v_x_2277_, 0);
v_vs_2336_ = lean_ctor_get(v_x_2277_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_x_2277_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2338_ = v_x_2277_;
v_isShared_2339_ = v_isSharedCheck_2350_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_vs_2336_);
lean_inc(v_ks_2335_);
lean_dec(v_x_2277_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2350_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2335_, v_x_2279_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v___x_2342_; 
if (v_isShared_2339_ == 0)
{
v___x_2342_ = v___x_2338_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_ks_2335_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_vs_2336_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
else
{
lean_object* v_val_2344_; lean_object* v_keys_x27_2345_; lean_object* v_vals_x27_2346_; lean_object* v___x_2348_; 
v_val_2344_ = lean_ctor_get(v___x_2340_, 0);
lean_inc_n(v_val_2344_, 2);
lean_dec_ref_known(v___x_2340_, 1);
v_keys_x27_2345_ = l_Array_eraseIdx___redArg(v_ks_2335_, v_val_2344_);
v_vals_x27_2346_ = l_Array_eraseIdx___redArg(v_vs_2336_, v_val_2344_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 1, v_vals_x27_2346_);
lean_ctor_set(v___x_2338_, 0, v_keys_x27_2345_);
v___x_2348_ = v___x_2338_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_keys_x27_2345_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_vals_x27_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg___boxed(lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_){
_start:
{
size_t v_x_19384__boxed_2354_; lean_object* v_res_2355_; 
v_x_19384__boxed_2354_ = lean_unbox_usize(v_x_2352_);
lean_dec(v_x_2352_);
v_res_2355_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2351_, v_x_19384__boxed_2354_, v_x_2353_);
lean_dec_ref(v_x_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2356_, lean_object* v_x_2357_){
_start:
{
size_t v___x_2358_; size_t v___x_2359_; size_t v___x_2360_; uint64_t v___x_2361_; size_t v_h_2362_; lean_object* v___x_2363_; 
v___x_2358_ = lean_ptr_addr(v_x_2357_);
v___x_2359_ = ((size_t)3ULL);
v___x_2360_ = lean_usize_shift_right(v___x_2358_, v___x_2359_);
v___x_2361_ = lean_usize_to_uint64(v___x_2360_);
v_h_2362_ = lean_uint64_to_usize(v___x_2361_);
v___x_2363_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2356_, v_h_2362_, v_x_2357_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2364_, lean_object* v_x_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2364_, v_x_2365_);
lean_dec_ref(v_x_2365_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
if (lean_obj_tag(v_as_2367_) == 0)
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_box(0);
v___x_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
else
{
lean_object* v_head_2381_; lean_object* v_tail_2382_; lean_object* v___x_2383_; 
v_head_2381_ = lean_ctor_get(v_as_2367_, 0);
lean_inc(v_head_2381_);
v_tail_2382_ = lean_ctor_get(v_as_2367_, 1);
lean_inc(v_tail_2382_);
lean_dec_ref_known(v_as_2367_, 2);
v___x_2383_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2381_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_dec_ref_known(v___x_2383_, 1);
v_as_2367_ = v_tail_2382_;
goto _start;
}
else
{
lean_dec(v_tail_2382_);
return v___x_2383_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec(v___y_2386_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2398_, lean_object* v_vals_2399_, lean_object* v_i_2400_, lean_object* v_k_2401_){
_start:
{
lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = lean_array_get_size(v_keys_2398_);
v___x_2403_ = lean_nat_dec_lt(v_i_2400_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; 
lean_dec(v_i_2400_);
v___x_2404_ = lean_box(0);
return v___x_2404_;
}
else
{
lean_object* v_k_x27_2405_; size_t v___x_2406_; size_t v___x_2407_; uint8_t v___x_2408_; 
v_k_x27_2405_ = lean_array_fget_borrowed(v_keys_2398_, v_i_2400_);
v___x_2406_ = lean_ptr_addr(v_k_2401_);
v___x_2407_ = lean_ptr_addr(v_k_x27_2405_);
v___x_2408_ = lean_usize_dec_eq(v___x_2406_, v___x_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_unsigned_to_nat(1u);
v___x_2410_ = lean_nat_add(v_i_2400_, v___x_2409_);
lean_dec(v_i_2400_);
v_i_2400_ = v___x_2410_;
goto _start;
}
else
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_array_fget_borrowed(v_vals_2399_, v_i_2400_);
lean_dec(v_i_2400_);
lean_inc(v___x_2412_);
v___x_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2414_, lean_object* v_vals_2415_, lean_object* v_i_2416_, lean_object* v_k_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2414_, v_vals_2415_, v_i_2416_, v_k_2417_);
lean_dec_ref(v_k_2417_);
lean_dec_ref(v_vals_2415_);
lean_dec_ref(v_keys_2414_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2419_, size_t v_x_2420_, lean_object* v_x_2421_){
_start:
{
if (lean_obj_tag(v_x_2419_) == 0)
{
lean_object* v_es_2422_; lean_object* v___x_2423_; size_t v___x_2424_; size_t v___x_2425_; lean_object* v_j_2426_; lean_object* v___x_2427_; 
v_es_2422_ = lean_ctor_get(v_x_2419_, 0);
v___x_2423_ = lean_box(2);
v___x_2424_ = ((size_t)31ULL);
v___x_2425_ = lean_usize_land(v_x_2420_, v___x_2424_);
v_j_2426_ = lean_usize_to_nat(v___x_2425_);
v___x_2427_ = lean_array_get_borrowed(v___x_2423_, v_es_2422_, v_j_2426_);
lean_dec(v_j_2426_);
switch(lean_obj_tag(v___x_2427_))
{
case 0:
{
lean_object* v_key_2428_; lean_object* v_val_2429_; size_t v___x_2430_; size_t v___x_2431_; uint8_t v___x_2432_; 
v_key_2428_ = lean_ctor_get(v___x_2427_, 0);
v_val_2429_ = lean_ctor_get(v___x_2427_, 1);
v___x_2430_ = lean_ptr_addr(v_x_2421_);
v___x_2431_ = lean_ptr_addr(v_key_2428_);
v___x_2432_ = lean_usize_dec_eq(v___x_2430_, v___x_2431_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_box(0);
return v___x_2433_;
}
else
{
lean_object* v___x_2434_; 
lean_inc(v_val_2429_);
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_val_2429_);
return v___x_2434_;
}
}
case 1:
{
lean_object* v_node_2435_; size_t v___x_2436_; size_t v___x_2437_; 
v_node_2435_ = lean_ctor_get(v___x_2427_, 0);
v___x_2436_ = ((size_t)5ULL);
v___x_2437_ = lean_usize_shift_right(v_x_2420_, v___x_2436_);
v_x_2419_ = v_node_2435_;
v_x_2420_ = v___x_2437_;
goto _start;
}
default: 
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_box(0);
return v___x_2439_;
}
}
}
else
{
lean_object* v_ks_2440_; lean_object* v_vs_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_ks_2440_ = lean_ctor_get(v_x_2419_, 0);
v_vs_2441_ = lean_ctor_get(v_x_2419_, 1);
v___x_2442_ = lean_unsigned_to_nat(0u);
v___x_2443_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2440_, v_vs_2441_, v___x_2442_, v_x_2421_);
return v___x_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2444_, lean_object* v_x_2445_, lean_object* v_x_2446_){
_start:
{
size_t v_x_19609__boxed_2447_; lean_object* v_res_2448_; 
v_x_19609__boxed_2447_ = lean_unbox_usize(v_x_2445_);
lean_dec(v_x_2445_);
v_res_2448_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2444_, v_x_19609__boxed_2447_, v_x_2446_);
lean_dec_ref(v_x_2446_);
lean_dec_ref(v_x_2444_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2449_, lean_object* v_x_2450_){
_start:
{
size_t v___x_2451_; size_t v___x_2452_; size_t v___x_2453_; uint64_t v___x_2454_; size_t v___x_2455_; lean_object* v___x_2456_; 
v___x_2451_ = lean_ptr_addr(v_x_2450_);
v___x_2452_ = ((size_t)3ULL);
v___x_2453_ = lean_usize_shift_right(v___x_2451_, v___x_2452_);
v___x_2454_ = lean_usize_to_uint64(v___x_2453_);
v___x_2455_ = lean_uint64_to_usize(v___x_2454_);
v___x_2456_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2449_, v___x_2455_, v_x_2450_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2457_, lean_object* v_x_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2457_, v_x_2458_);
lean_dec_ref(v_x_2458_);
lean_dec_ref(v_x_2457_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2460_, lean_object* v_b_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
if (lean_obj_tag(v_as_x27_2460_) == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2473_, 0, v_b_2461_);
return v___x_2473_;
}
else
{
lean_object* v_head_2474_; lean_object* v_tail_2475_; lean_object* v___x_2476_; lean_object* v_toGoalState_2477_; lean_object* v_ematch_2478_; lean_object* v_delayedThmInsts_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_head_2474_ = lean_ctor_get(v_as_x27_2460_, 0);
v_tail_2475_ = lean_ctor_get(v_as_x27_2460_, 1);
v___x_2476_ = lean_st_ref_get(v___y_2462_);
v_toGoalState_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_ref(v_toGoalState_2477_);
lean_dec(v___x_2476_);
v_ematch_2478_ = lean_ctor_get(v_toGoalState_2477_, 12);
lean_inc_ref(v_ematch_2478_);
lean_dec_ref(v_toGoalState_2477_);
v_delayedThmInsts_2479_ = lean_ctor_get(v_ematch_2478_, 10);
lean_inc_ref(v_delayedThmInsts_2479_);
lean_dec_ref(v_ematch_2478_);
v___x_2480_ = lean_box(0);
v___x_2481_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2479_, v_head_2474_);
lean_dec_ref(v_delayedThmInsts_2479_);
if (lean_obj_tag(v___x_2481_) == 1)
{
lean_object* v_val_2482_; lean_object* v___x_2483_; lean_object* v_toGoalState_2484_; lean_object* v_ematch_2485_; lean_object* v_mvarId_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2540_; 
v_val_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_val_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v___x_2483_ = lean_st_ref_take(v___y_2462_);
v_toGoalState_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc_ref(v_toGoalState_2484_);
v_ematch_2485_ = lean_ctor_get(v_toGoalState_2484_, 12);
lean_inc_ref(v_ematch_2485_);
v_mvarId_2486_ = lean_ctor_get(v___x_2483_, 1);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; 
v_unused_2541_ = lean_ctor_get(v___x_2483_, 0);
lean_dec(v_unused_2541_);
v___x_2488_ = v___x_2483_;
v_isShared_2489_ = v_isSharedCheck_2540_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_mvarId_2486_);
lean_dec(v___x_2483_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2540_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v_nextDeclIdx_2490_; lean_object* v_enodeMap_2491_; lean_object* v_exprs_2492_; lean_object* v_parents_2493_; lean_object* v_congrTable_2494_; lean_object* v_appMap_2495_; lean_object* v_indicesFound_2496_; lean_object* v_newFacts_2497_; uint8_t v_inconsistent_2498_; lean_object* v_nextIdx_2499_; lean_object* v_newRawFacts_2500_; lean_object* v_facts_2501_; lean_object* v_extThms_2502_; lean_object* v_inj_2503_; lean_object* v_split_2504_; lean_object* v_clean_2505_; lean_object* v_sstates_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2538_; 
v_nextDeclIdx_2490_ = lean_ctor_get(v_toGoalState_2484_, 0);
v_enodeMap_2491_ = lean_ctor_get(v_toGoalState_2484_, 1);
v_exprs_2492_ = lean_ctor_get(v_toGoalState_2484_, 2);
v_parents_2493_ = lean_ctor_get(v_toGoalState_2484_, 3);
v_congrTable_2494_ = lean_ctor_get(v_toGoalState_2484_, 4);
v_appMap_2495_ = lean_ctor_get(v_toGoalState_2484_, 5);
v_indicesFound_2496_ = lean_ctor_get(v_toGoalState_2484_, 6);
v_newFacts_2497_ = lean_ctor_get(v_toGoalState_2484_, 7);
v_inconsistent_2498_ = lean_ctor_get_uint8(v_toGoalState_2484_, sizeof(void*)*17);
v_nextIdx_2499_ = lean_ctor_get(v_toGoalState_2484_, 8);
v_newRawFacts_2500_ = lean_ctor_get(v_toGoalState_2484_, 9);
v_facts_2501_ = lean_ctor_get(v_toGoalState_2484_, 10);
v_extThms_2502_ = lean_ctor_get(v_toGoalState_2484_, 11);
v_inj_2503_ = lean_ctor_get(v_toGoalState_2484_, 13);
v_split_2504_ = lean_ctor_get(v_toGoalState_2484_, 14);
v_clean_2505_ = lean_ctor_get(v_toGoalState_2484_, 15);
v_sstates_2506_ = lean_ctor_get(v_toGoalState_2484_, 16);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_toGoalState_2484_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; 
v_unused_2539_ = lean_ctor_get(v_toGoalState_2484_, 12);
lean_dec(v_unused_2539_);
v___x_2508_ = v_toGoalState_2484_;
v_isShared_2509_ = v_isSharedCheck_2538_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_sstates_2506_);
lean_inc(v_clean_2505_);
lean_inc(v_split_2504_);
lean_inc(v_inj_2503_);
lean_inc(v_extThms_2502_);
lean_inc(v_facts_2501_);
lean_inc(v_newRawFacts_2500_);
lean_inc(v_nextIdx_2499_);
lean_inc(v_newFacts_2497_);
lean_inc(v_indicesFound_2496_);
lean_inc(v_appMap_2495_);
lean_inc(v_congrTable_2494_);
lean_inc(v_parents_2493_);
lean_inc(v_exprs_2492_);
lean_inc(v_enodeMap_2491_);
lean_inc(v_nextDeclIdx_2490_);
lean_dec(v_toGoalState_2484_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2538_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v_thmMap_2510_; lean_object* v_gmt_2511_; lean_object* v_thms_2512_; lean_object* v_newThms_2513_; lean_object* v_numInstances_2514_; lean_object* v_numDelayedInstances_2515_; lean_object* v_num_2516_; lean_object* v_preInstances_2517_; lean_object* v_nextThmIdx_2518_; lean_object* v_matchEqNames_2519_; lean_object* v_delayedThmInsts_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2537_; 
v_thmMap_2510_ = lean_ctor_get(v_ematch_2485_, 0);
v_gmt_2511_ = lean_ctor_get(v_ematch_2485_, 1);
v_thms_2512_ = lean_ctor_get(v_ematch_2485_, 2);
v_newThms_2513_ = lean_ctor_get(v_ematch_2485_, 3);
v_numInstances_2514_ = lean_ctor_get(v_ematch_2485_, 4);
v_numDelayedInstances_2515_ = lean_ctor_get(v_ematch_2485_, 5);
v_num_2516_ = lean_ctor_get(v_ematch_2485_, 6);
v_preInstances_2517_ = lean_ctor_get(v_ematch_2485_, 7);
v_nextThmIdx_2518_ = lean_ctor_get(v_ematch_2485_, 8);
v_matchEqNames_2519_ = lean_ctor_get(v_ematch_2485_, 9);
v_delayedThmInsts_2520_ = lean_ctor_get(v_ematch_2485_, 10);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_ematch_2485_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2522_ = v_ematch_2485_;
v_isShared_2523_ = v_isSharedCheck_2537_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_delayedThmInsts_2520_);
lean_inc(v_matchEqNames_2519_);
lean_inc(v_nextThmIdx_2518_);
lean_inc(v_preInstances_2517_);
lean_inc(v_num_2516_);
lean_inc(v_numDelayedInstances_2515_);
lean_inc(v_numInstances_2514_);
lean_inc(v_newThms_2513_);
lean_inc(v_thms_2512_);
lean_inc(v_gmt_2511_);
lean_inc(v_thmMap_2510_);
lean_dec(v_ematch_2485_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2537_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2526_; 
v___x_2524_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2520_, v_head_2474_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 10, v___x_2524_);
v___x_2526_ = v___x_2522_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_thmMap_2510_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_gmt_2511_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_thms_2512_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_newThms_2513_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_numInstances_2514_);
lean_ctor_set(v_reuseFailAlloc_2536_, 5, v_numDelayedInstances_2515_);
lean_ctor_set(v_reuseFailAlloc_2536_, 6, v_num_2516_);
lean_ctor_set(v_reuseFailAlloc_2536_, 7, v_preInstances_2517_);
lean_ctor_set(v_reuseFailAlloc_2536_, 8, v_nextThmIdx_2518_);
lean_ctor_set(v_reuseFailAlloc_2536_, 9, v_matchEqNames_2519_);
lean_ctor_set(v_reuseFailAlloc_2536_, 10, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2528_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 12, v___x_2526_);
v___x_2528_ = v___x_2508_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_nextDeclIdx_2490_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_enodeMap_2491_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_exprs_2492_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v_parents_2493_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v_congrTable_2494_);
lean_ctor_set(v_reuseFailAlloc_2535_, 5, v_appMap_2495_);
lean_ctor_set(v_reuseFailAlloc_2535_, 6, v_indicesFound_2496_);
lean_ctor_set(v_reuseFailAlloc_2535_, 7, v_newFacts_2497_);
lean_ctor_set(v_reuseFailAlloc_2535_, 8, v_nextIdx_2499_);
lean_ctor_set(v_reuseFailAlloc_2535_, 9, v_newRawFacts_2500_);
lean_ctor_set(v_reuseFailAlloc_2535_, 10, v_facts_2501_);
lean_ctor_set(v_reuseFailAlloc_2535_, 11, v_extThms_2502_);
lean_ctor_set(v_reuseFailAlloc_2535_, 12, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2535_, 13, v_inj_2503_);
lean_ctor_set(v_reuseFailAlloc_2535_, 14, v_split_2504_);
lean_ctor_set(v_reuseFailAlloc_2535_, 15, v_clean_2505_);
lean_ctor_set(v_reuseFailAlloc_2535_, 16, v_sstates_2506_);
lean_ctor_set_uint8(v_reuseFailAlloc_2535_, sizeof(void*)*17, v_inconsistent_2498_);
v___x_2528_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2530_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2528_);
v___x_2530_ = v___x_2488_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_mvarId_2486_);
v___x_2530_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_st_ref_put(v___y_2462_, v___x_2530_);
v___x_2532_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2482_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_dec_ref_known(v___x_2532_, 1);
v_as_x27_2460_ = v_tail_2475_;
v_b_2461_ = v___x_2480_;
goto _start;
}
else
{
return v___x_2532_;
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
lean_dec(v___x_2481_);
v_as_x27_2460_ = v_tail_2475_;
v_b_2461_ = v___x_2480_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2543_, lean_object* v_b_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2543_, v_b_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
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
lean_dec(v_as_x27_2543_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2558_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2598_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2598_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2598_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
uint8_t v___x_2574_; 
v___x_2574_ = lean_unbox(v_a_2570_);
lean_dec(v_a_2570_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; lean_object* v_toGoalState_2576_; lean_object* v_ematch_2577_; lean_object* v_delayedThmInsts_2578_; uint8_t v___x_2579_; 
v___x_2575_ = lean_st_ref_get(v_a_2558_);
v_toGoalState_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc_ref(v_toGoalState_2576_);
lean_dec(v___x_2575_);
v_ematch_2577_ = lean_ctor_get(v_toGoalState_2576_, 12);
lean_inc_ref(v_ematch_2577_);
lean_dec_ref(v_toGoalState_2576_);
v_delayedThmInsts_2578_ = lean_ctor_get(v_ematch_2577_, 10);
lean_inc_ref(v_delayedThmInsts_2578_);
lean_dec_ref(v_ematch_2577_);
v___x_2579_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2578_);
lean_dec_ref(v_delayedThmInsts_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_del_object(v___x_2572_);
v___x_2580_ = lean_box(0);
v___x_2581_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2557_, v___x_2580_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v___x_2581_, 0);
lean_dec(v_unused_2589_);
v___x_2583_ = v___x_2581_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_dec(v___x_2581_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2580_);
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2580_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
else
{
return v___x_2581_;
}
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
v___x_2590_ = lean_box(0);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2590_);
v___x_2592_ = v___x_2572_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = lean_box(0);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v___x_2594_);
v___x_2596_ = v___x_2572_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
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
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
v_a_2599_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2569_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2569_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec(v_toPropagateDown_2607_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2621_, v_x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2624_, v_x_2625_, v_x_2626_);
lean_dec_ref(v_x_2626_);
lean_dec_ref(v_x_2625_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2628_, lean_object* v_x_2629_, lean_object* v_x_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2629_, v_x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2632_, lean_object* v_x_2633_, lean_object* v_x_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2632_, v_x_2633_, v_x_2634_);
lean_dec_ref(v_x_2634_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2636_, lean_object* v_as_x27_2637_, lean_object* v_b_2638_, lean_object* v_a_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2637_, v_b_2638_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2652_, lean_object* v_as_x27_2653_, lean_object* v_b_2654_, lean_object* v_a_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2652_, v_as_x27_2653_, v_b_2654_, v_a_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec(v_as_x27_2653_);
lean_dec(v_as_2652_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2668_, lean_object* v_x_2669_, size_t v_x_2670_, lean_object* v_x_2671_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2669_, v_x_2670_, v_x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_){
_start:
{
size_t v_x_19914__boxed_2677_; lean_object* v_res_2678_; 
v_x_19914__boxed_2677_ = lean_unbox_usize(v_x_2675_);
lean_dec(v_x_2675_);
v_res_2678_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2673_, v_x_2674_, v_x_19914__boxed_2677_, v_x_2676_);
lean_dec_ref(v_x_2676_);
lean_dec_ref(v_x_2674_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2679_, lean_object* v_x_2680_, size_t v_x_2681_, lean_object* v_x_2682_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2680_, v_x_2681_, v_x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2684_, lean_object* v_x_2685_, lean_object* v_x_2686_, lean_object* v_x_2687_){
_start:
{
size_t v_x_19925__boxed_2688_; lean_object* v_res_2689_; 
v_x_19925__boxed_2688_ = lean_unbox_usize(v_x_2686_);
lean_dec(v_x_2686_);
v_res_2689_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2684_, v_x_2685_, v_x_19925__boxed_2688_, v_x_2687_);
lean_dec_ref(v_x_2687_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2690_, lean_object* v_keys_2691_, lean_object* v_vals_2692_, lean_object* v_heq_2693_, lean_object* v_i_2694_, lean_object* v_k_2695_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2691_, v_vals_2692_, v_i_2694_, v_k_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2697_, lean_object* v_keys_2698_, lean_object* v_vals_2699_, lean_object* v_heq_2700_, lean_object* v_i_2701_, lean_object* v_k_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2697_, v_keys_2698_, v_vals_2699_, v_heq_2700_, v_i_2701_, v_k_2702_);
lean_dec_ref(v_k_2702_);
lean_dec_ref(v_vals_2699_);
lean_dec_ref(v_keys_2698_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2704_, lean_object* v_keys_2705_, lean_object* v_vals_2706_, lean_object* v_i_2707_, lean_object* v_k_2708_){
_start:
{
lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = lean_array_get_size(v_keys_2705_);
v___x_2710_ = lean_nat_dec_lt(v_i_2707_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; 
lean_dec_ref(v_k_2708_);
lean_dec(v_i_2707_);
v___x_2711_ = lean_box(0);
return v___x_2711_;
}
else
{
lean_object* v_k_x27_2712_; uint8_t v___x_2713_; 
v_k_x27_2712_ = lean_array_fget_borrowed(v_keys_2705_, v_i_2707_);
lean_inc(v_k_x27_2712_);
lean_inc_ref(v_k_2708_);
v___x_2713_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2704_, v_k_2708_, v_k_x27_2712_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = lean_unsigned_to_nat(1u);
v___x_2715_ = lean_nat_add(v_i_2707_, v___x_2714_);
lean_dec(v_i_2707_);
v_i_2707_ = v___x_2715_;
goto _start;
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_dec_ref(v_k_2708_);
v___x_2717_ = lean_array_fget_borrowed(v_vals_2706_, v_i_2707_);
lean_dec(v_i_2707_);
lean_inc(v___x_2717_);
lean_inc(v_k_x27_2712_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_k_x27_2712_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
return v___x_2719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2720_, lean_object* v_keys_2721_, lean_object* v_vals_2722_, lean_object* v_i_2723_, lean_object* v_k_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2720_, v_keys_2721_, v_vals_2722_, v_i_2723_, v_k_2724_);
lean_dec_ref(v_vals_2722_);
lean_dec_ref(v_keys_2721_);
lean_dec_ref(v___x_2720_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2726_, lean_object* v_x_2727_, size_t v_x_2728_, lean_object* v_x_2729_){
_start:
{
if (lean_obj_tag(v_x_2727_) == 0)
{
lean_object* v_es_2730_; lean_object* v___x_2731_; size_t v___x_2732_; size_t v___x_2733_; lean_object* v_j_2734_; lean_object* v___x_2735_; 
v_es_2730_ = lean_ctor_get(v_x_2727_, 0);
lean_inc_ref(v_es_2730_);
lean_dec_ref_known(v_x_2727_, 1);
v___x_2731_ = lean_box(2);
v___x_2732_ = ((size_t)31ULL);
v___x_2733_ = lean_usize_land(v_x_2728_, v___x_2732_);
v_j_2734_ = lean_usize_to_nat(v___x_2733_);
v___x_2735_ = lean_array_get(v___x_2731_, v_es_2730_, v_j_2734_);
lean_dec(v_j_2734_);
lean_dec_ref(v_es_2730_);
switch(lean_obj_tag(v___x_2735_))
{
case 0:
{
lean_object* v_key_2736_; lean_object* v_val_2737_; uint8_t v___x_2738_; 
v_key_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_n(v_key_2736_, 2);
v_val_2737_ = lean_ctor_get(v___x_2735_, 1);
lean_inc(v_val_2737_);
lean_dec_ref_known(v___x_2735_, 2);
v___x_2738_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2726_, v_x_2729_, v_key_2736_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; 
lean_dec(v_val_2737_);
lean_dec(v_key_2736_);
v___x_2739_ = lean_box(0);
return v___x_2739_;
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v_key_2736_);
lean_ctor_set(v___x_2740_, 1, v_val_2737_);
v___x_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
return v___x_2741_;
}
}
case 1:
{
lean_object* v_node_2742_; size_t v___x_2743_; size_t v___x_2744_; 
v_node_2742_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_node_2742_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2743_ = ((size_t)5ULL);
v___x_2744_ = lean_usize_shift_right(v_x_2728_, v___x_2743_);
v_x_2727_ = v_node_2742_;
v_x_2728_ = v___x_2744_;
goto _start;
}
default: 
{
lean_object* v___x_2746_; 
lean_dec_ref(v_x_2729_);
v___x_2746_ = lean_box(0);
return v___x_2746_;
}
}
}
else
{
lean_object* v_ks_2747_; lean_object* v_vs_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_ks_2747_ = lean_ctor_get(v_x_2727_, 0);
lean_inc_ref(v_ks_2747_);
v_vs_2748_ = lean_ctor_get(v_x_2727_, 1);
lean_inc_ref(v_vs_2748_);
lean_dec_ref_known(v_x_2727_, 2);
v___x_2749_ = lean_unsigned_to_nat(0u);
v___x_2750_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2726_, v_ks_2747_, v_vs_2748_, v___x_2749_, v_x_2729_);
lean_dec_ref(v_vs_2748_);
lean_dec_ref(v_ks_2747_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_){
_start:
{
size_t v_x_25943__boxed_2755_; lean_object* v_res_2756_; 
v_x_25943__boxed_2755_ = lean_unbox_usize(v_x_2753_);
lean_dec(v_x_2753_);
v_res_2756_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2751_, v_x_2752_, v_x_25943__boxed_2755_, v_x_2754_);
lean_dec_ref(v___x_2751_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2757_, lean_object* v_x_2758_, lean_object* v_x_2759_){
_start:
{
uint64_t v___x_2760_; size_t v___x_2761_; lean_object* v___x_2762_; 
lean_inc_ref(v_x_2759_);
v___x_2760_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2757_, v_x_2759_);
v___x_2761_ = lean_uint64_to_usize(v___x_2760_);
lean_inc_ref(v_x_2758_);
v___x_2762_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2757_, v_x_2758_, v___x_2761_, v_x_2759_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2763_, lean_object* v_x_2764_, lean_object* v_x_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2763_, v_x_2764_, v_x_2765_);
lean_dec_ref(v_x_2764_);
lean_dec_ref(v___x_2763_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2767_, lean_object* v_x_2768_, lean_object* v_x_2769_, lean_object* v_x_2770_, lean_object* v_x_2771_){
_start:
{
lean_object* v_ks_2772_; lean_object* v_vs_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2797_; 
v_ks_2772_ = lean_ctor_get(v_x_2768_, 0);
v_vs_2773_ = lean_ctor_get(v_x_2768_, 1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_x_2768_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2775_ = v_x_2768_;
v_isShared_2776_ = v_isSharedCheck_2797_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_vs_2773_);
lean_inc(v_ks_2772_);
lean_dec(v_x_2768_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2797_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = lean_array_get_size(v_ks_2772_);
v___x_2778_ = lean_nat_dec_lt(v_x_2769_, v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
lean_dec(v_x_2769_);
v___x_2779_ = lean_array_push(v_ks_2772_, v_x_2770_);
v___x_2780_ = lean_array_push(v_vs_2773_, v_x_2771_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 1, v___x_2780_);
lean_ctor_set(v___x_2775_, 0, v___x_2779_);
v___x_2782_ = v___x_2775_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
else
{
lean_object* v_k_x27_2784_; uint8_t v___x_2785_; 
v_k_x27_2784_ = lean_array_fget_borrowed(v_ks_2772_, v_x_2769_);
lean_inc(v_k_x27_2784_);
lean_inc_ref(v_x_2770_);
v___x_2785_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2767_, v_x_2770_, v_k_x27_2784_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2787_; 
if (v_isShared_2776_ == 0)
{
v___x_2787_ = v___x_2775_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_ks_2772_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_vs_2773_);
v___x_2787_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_unsigned_to_nat(1u);
v___x_2789_ = lean_nat_add(v_x_2769_, v___x_2788_);
lean_dec(v_x_2769_);
v_x_2768_ = v___x_2787_;
v_x_2769_ = v___x_2789_;
goto _start;
}
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2792_ = lean_array_fset(v_ks_2772_, v_x_2769_, v_x_2770_);
v___x_2793_ = lean_array_fset(v_vs_2773_, v_x_2769_, v_x_2771_);
lean_dec(v_x_2769_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 1, v___x_2793_);
lean_ctor_set(v___x_2775_, 0, v___x_2792_);
v___x_2795_ = v___x_2775_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2798_, lean_object* v_x_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_, lean_object* v_x_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2798_, v_x_2799_, v_x_2800_, v_x_2801_, v_x_2802_);
lean_dec_ref(v___x_2798_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2804_, lean_object* v_n_2805_, lean_object* v_k_2806_, lean_object* v_v_2807_){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = lean_unsigned_to_nat(0u);
v___x_2809_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2804_, v_n_2805_, v___x_2808_, v_k_2806_, v_v_2807_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2810_, lean_object* v_n_2811_, lean_object* v_k_2812_, lean_object* v_v_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2810_, v_n_2811_, v_k_2812_, v_v_2813_);
lean_dec_ref(v___x_2810_);
return v_res_2814_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2816_, lean_object* v_x_2817_, size_t v_x_2818_, size_t v_x_2819_, lean_object* v_x_2820_, lean_object* v_x_2821_){
_start:
{
if (lean_obj_tag(v_x_2817_) == 0)
{
lean_object* v_es_2822_; size_t v___x_2823_; size_t v___x_2824_; lean_object* v_j_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_es_2822_ = lean_ctor_get(v_x_2817_, 0);
v___x_2823_ = ((size_t)31ULL);
v___x_2824_ = lean_usize_land(v_x_2818_, v___x_2823_);
v_j_2825_ = lean_usize_to_nat(v___x_2824_);
v___x_2826_ = lean_array_get_size(v_es_2822_);
v___x_2827_ = lean_nat_dec_lt(v_j_2825_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_dec(v_j_2825_);
lean_dec(v_x_2821_);
lean_dec_ref(v_x_2820_);
return v_x_2817_;
}
else
{
lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2866_; 
lean_inc_ref(v_es_2822_);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_x_2817_);
if (v_isSharedCheck_2866_ == 0)
{
lean_object* v_unused_2867_; 
v_unused_2867_ = lean_ctor_get(v_x_2817_, 0);
lean_dec(v_unused_2867_);
v___x_2829_ = v_x_2817_;
v_isShared_2830_ = v_isSharedCheck_2866_;
goto v_resetjp_2828_;
}
else
{
lean_dec(v_x_2817_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2866_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_v_2831_; lean_object* v___x_2832_; lean_object* v_xs_x27_2833_; lean_object* v___y_2835_; 
v_v_2831_ = lean_array_fget(v_es_2822_, v_j_2825_);
v___x_2832_ = lean_box(0);
v_xs_x27_2833_ = lean_array_fset(v_es_2822_, v_j_2825_, v___x_2832_);
switch(lean_obj_tag(v_v_2831_))
{
case 0:
{
lean_object* v_key_2840_; lean_object* v_val_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2851_; 
v_key_2840_ = lean_ctor_get(v_v_2831_, 0);
v_val_2841_ = lean_ctor_get(v_v_2831_, 1);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_v_2831_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2843_ = v_v_2831_;
v_isShared_2844_ = v_isSharedCheck_2851_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_val_2841_);
lean_inc(v_key_2840_);
lean_dec(v_v_2831_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2851_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
uint8_t v___x_2845_; 
lean_inc(v_key_2840_);
lean_inc_ref(v_x_2820_);
v___x_2845_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2816_, v_x_2820_, v_key_2840_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_del_object(v___x_2843_);
v___x_2846_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2840_, v_val_2841_, v_x_2820_, v_x_2821_);
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
v___y_2835_ = v___x_2847_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2849_; 
lean_dec(v_val_2841_);
lean_dec(v_key_2840_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 1, v_x_2821_);
lean_ctor_set(v___x_2843_, 0, v_x_2820_);
v___x_2849_ = v___x_2843_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_x_2820_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_x_2821_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
v___y_2835_ = v___x_2849_;
goto v___jp_2834_;
}
}
}
}
case 1:
{
lean_object* v_node_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2864_; 
v_node_2852_ = lean_ctor_get(v_v_2831_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_v_2831_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2854_ = v_v_2831_;
v_isShared_2855_ = v_isSharedCheck_2864_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_node_2852_);
lean_dec(v_v_2831_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2864_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
size_t v___x_2856_; size_t v___x_2857_; size_t v___x_2858_; size_t v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
v___x_2856_ = ((size_t)5ULL);
v___x_2857_ = lean_usize_shift_right(v_x_2818_, v___x_2856_);
v___x_2858_ = ((size_t)1ULL);
v___x_2859_ = lean_usize_add(v_x_2819_, v___x_2858_);
v___x_2860_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2816_, v_node_2852_, v___x_2857_, v___x_2859_, v_x_2820_, v_x_2821_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2860_);
v___x_2862_ = v___x_2854_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
v___y_2835_ = v___x_2862_;
goto v___jp_2834_;
}
}
}
default: 
{
lean_object* v___x_2865_; 
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v_x_2820_);
lean_ctor_set(v___x_2865_, 1, v_x_2821_);
v___y_2835_ = v___x_2865_;
goto v___jp_2834_;
}
}
v___jp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2836_ = lean_array_fset(v_xs_x27_2833_, v_j_2825_, v___y_2835_);
lean_dec(v_j_2825_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2836_);
v___x_2838_ = v___x_2829_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
else
{
lean_object* v_ks_2868_; lean_object* v_vs_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2887_; 
v_ks_2868_ = lean_ctor_get(v_x_2817_, 0);
v_vs_2869_ = lean_ctor_get(v_x_2817_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_x_2817_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2871_ = v_x_2817_;
v_isShared_2872_ = v_isSharedCheck_2887_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_vs_2869_);
lean_inc(v_ks_2868_);
lean_dec(v_x_2817_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2887_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_ks_2868_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_vs_2869_);
v___x_2874_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v_newNode_2875_; size_t v___x_2876_; uint8_t v___x_2877_; 
v_newNode_2875_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2816_, v___x_2874_, v_x_2820_, v_x_2821_);
v___x_2876_ = ((size_t)7ULL);
v___x_2877_ = lean_usize_dec_le(v___x_2876_, v_x_2819_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2878_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2875_);
v___x_2879_ = lean_unsigned_to_nat(4u);
v___x_2880_ = lean_nat_dec_lt(v___x_2878_, v___x_2879_);
lean_dec(v___x_2878_);
if (v___x_2880_ == 0)
{
lean_object* v_ks_2881_; lean_object* v_vs_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_ks_2881_ = lean_ctor_get(v_newNode_2875_, 0);
lean_inc_ref(v_ks_2881_);
v_vs_2882_ = lean_ctor_get(v_newNode_2875_, 1);
lean_inc_ref(v_vs_2882_);
lean_dec_ref(v_newNode_2875_);
v___x_2883_ = lean_unsigned_to_nat(0u);
v___x_2884_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2885_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2816_, v_x_2819_, v_ks_2881_, v_vs_2882_, v___x_2883_, v___x_2884_);
lean_dec_ref(v_vs_2882_);
lean_dec_ref(v_ks_2881_);
return v___x_2885_;
}
else
{
return v_newNode_2875_;
}
}
else
{
return v_newNode_2875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2888_, size_t v_depth_2889_, lean_object* v_keys_2890_, lean_object* v_vals_2891_, lean_object* v_i_2892_, lean_object* v_entries_2893_){
_start:
{
lean_object* v___x_2894_; uint8_t v___x_2895_; 
v___x_2894_ = lean_array_get_size(v_keys_2890_);
v___x_2895_ = lean_nat_dec_lt(v_i_2892_, v___x_2894_);
if (v___x_2895_ == 0)
{
lean_dec(v_i_2892_);
return v_entries_2893_;
}
else
{
lean_object* v_k_2896_; lean_object* v_v_2897_; uint64_t v___x_2898_; size_t v_h_2899_; size_t v___x_2900_; lean_object* v___x_2901_; size_t v___x_2902_; size_t v___x_2903_; size_t v___x_2904_; size_t v_h_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_k_2896_ = lean_array_fget_borrowed(v_keys_2890_, v_i_2892_);
v_v_2897_ = lean_array_fget_borrowed(v_vals_2891_, v_i_2892_);
lean_inc_n(v_k_2896_, 2);
v___x_2898_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2888_, v_k_2896_);
v_h_2899_ = lean_uint64_to_usize(v___x_2898_);
v___x_2900_ = ((size_t)5ULL);
v___x_2901_ = lean_unsigned_to_nat(1u);
v___x_2902_ = ((size_t)1ULL);
v___x_2903_ = lean_usize_sub(v_depth_2889_, v___x_2902_);
v___x_2904_ = lean_usize_mul(v___x_2900_, v___x_2903_);
v_h_2905_ = lean_usize_shift_right(v_h_2899_, v___x_2904_);
v___x_2906_ = lean_nat_add(v_i_2892_, v___x_2901_);
lean_dec(v_i_2892_);
lean_inc(v_v_2897_);
v___x_2907_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2888_, v_entries_2893_, v_h_2905_, v_depth_2889_, v_k_2896_, v_v_2897_);
v_i_2892_ = v___x_2906_;
v_entries_2893_ = v___x_2907_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2909_, lean_object* v_depth_2910_, lean_object* v_keys_2911_, lean_object* v_vals_2912_, lean_object* v_i_2913_, lean_object* v_entries_2914_){
_start:
{
size_t v_depth_boxed_2915_; lean_object* v_res_2916_; 
v_depth_boxed_2915_ = lean_unbox_usize(v_depth_2910_);
lean_dec(v_depth_2910_);
v_res_2916_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2909_, v_depth_boxed_2915_, v_keys_2911_, v_vals_2912_, v_i_2913_, v_entries_2914_);
lean_dec_ref(v_vals_2912_);
lean_dec_ref(v_keys_2911_);
lean_dec_ref(v___x_2909_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_){
_start:
{
size_t v_x_26097__boxed_2923_; size_t v_x_26098__boxed_2924_; lean_object* v_res_2925_; 
v_x_26097__boxed_2923_ = lean_unbox_usize(v_x_2919_);
lean_dec(v_x_2919_);
v_x_26098__boxed_2924_ = lean_unbox_usize(v_x_2920_);
lean_dec(v_x_2920_);
v_res_2925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2917_, v_x_2918_, v_x_26097__boxed_2923_, v_x_26098__boxed_2924_, v_x_2921_, v_x_2922_);
lean_dec_ref(v___x_2917_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2926_, lean_object* v_x_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
uint64_t v___x_2930_; size_t v___x_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
lean_inc_ref(v_x_2928_);
v___x_2930_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2926_, v_x_2928_);
v___x_2931_ = lean_uint64_to_usize(v___x_2930_);
v___x_2932_ = ((size_t)1ULL);
v___x_2933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2926_, v_x_2927_, v___x_2931_, v___x_2932_, v_x_2928_, v_x_2929_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2934_, lean_object* v_x_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2934_, v_x_2935_, v_x_2936_, v_x_2937_);
lean_dec_ref(v___x_2934_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2943_, lean_object* v_rootNew_2944_, uint8_t v_a_2945_, lean_object* v_a_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___x_2954_; lean_object* v_snd_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3124_; 
v___x_2954_ = lean_st_ref_get(v___y_2947_);
v_snd_2955_ = lean_ctor_get(v_a_2946_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_a_2946_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_a_2946_, 0);
lean_dec(v_unused_3125_);
v___x_2957_ = v_a_2946_;
v_isShared_2958_ = v_isSharedCheck_3124_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_snd_2955_);
lean_dec(v_a_2946_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3124_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; 
lean_inc(v_snd_2955_);
v___x_2959_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2954_, v_snd_2955_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___x_2954_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_3115_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_3115_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_3115_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v_self_2964_; lean_object* v_next_2965_; lean_object* v_congr_2966_; lean_object* v_target_x3f_2967_; lean_object* v_proof_x3f_2968_; uint8_t v_flipped_2969_; lean_object* v_size_2970_; uint8_t v_interpreted_2971_; uint8_t v_ctor_2972_; uint8_t v_hasLambdas_2973_; uint8_t v_heqProofs_2974_; lean_object* v_idx_2975_; lean_object* v_generation_2976_; lean_object* v_mt_2977_; lean_object* v_sTerms_2978_; uint8_t v_funCC_2979_; lean_object* v_ematchDiagSource_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3113_; 
v_self_2964_ = lean_ctor_get(v_a_2960_, 0);
v_next_2965_ = lean_ctor_get(v_a_2960_, 1);
v_congr_2966_ = lean_ctor_get(v_a_2960_, 3);
v_target_x3f_2967_ = lean_ctor_get(v_a_2960_, 4);
v_proof_x3f_2968_ = lean_ctor_get(v_a_2960_, 5);
v_flipped_2969_ = lean_ctor_get_uint8(v_a_2960_, sizeof(void*)*12);
v_size_2970_ = lean_ctor_get(v_a_2960_, 6);
v_interpreted_2971_ = lean_ctor_get_uint8(v_a_2960_, sizeof(void*)*12 + 1);
v_ctor_2972_ = lean_ctor_get_uint8(v_a_2960_, sizeof(void*)*12 + 2);
v_hasLambdas_2973_ = lean_ctor_get_uint8(v_a_2960_, sizeof(void*)*12 + 3);
v_heqProofs_2974_ = lean_ctor_get_uint8(v_a_2960_, sizeof(void*)*12 + 4);
v_idx_2975_ = lean_ctor_get(v_a_2960_, 7);
v_generation_2976_ = lean_ctor_get(v_a_2960_, 8);
v_mt_2977_ = lean_ctor_get(v_a_2960_, 9);
v_sTerms_2978_ = lean_ctor_get(v_a_2960_, 10);
v_funCC_2979_ = lean_ctor_get_uint8(v_a_2960_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2980_ = lean_ctor_get(v_a_2960_, 11);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_a_2960_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; 
v_unused_3114_ = lean_ctor_get(v_a_2960_, 2);
lean_dec(v_unused_3114_);
v___x_2982_ = v_a_2960_;
v_isShared_2983_ = v_isSharedCheck_3113_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_ematchDiagSource_2980_);
lean_inc(v_sTerms_2978_);
lean_inc(v_mt_2977_);
lean_inc(v_generation_2976_);
lean_inc(v_idx_2975_);
lean_inc(v_size_2970_);
lean_inc(v_proof_x3f_2968_);
lean_inc(v_target_x3f_2967_);
lean_inc(v_congr_2966_);
lean_inc(v_next_2965_);
lean_inc(v_self_2964_);
lean_dec(v_a_2960_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3113_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___y_3001_; lean_object* v___x_3011_; 
v___x_2984_ = lean_box(0);
lean_inc(v_ematchDiagSource_2980_);
lean_inc(v_sTerms_2978_);
lean_inc(v_mt_2977_);
lean_inc(v_generation_2976_);
lean_inc(v_idx_2975_);
lean_inc(v_size_2970_);
lean_inc(v_proof_x3f_2968_);
lean_inc(v_target_x3f_2967_);
lean_inc_ref(v_rootNew_2944_);
lean_inc_ref(v_next_2965_);
lean_inc_ref(v_self_2964_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 2, v_rootNew_2944_);
v___x_3011_ = v___x_2982_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_self_2964_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_next_2965_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_rootNew_2944_);
lean_ctor_set(v_reuseFailAlloc_3112_, 3, v_congr_2966_);
lean_ctor_set(v_reuseFailAlloc_3112_, 4, v_target_x3f_2967_);
lean_ctor_set(v_reuseFailAlloc_3112_, 5, v_proof_x3f_2968_);
lean_ctor_set(v_reuseFailAlloc_3112_, 6, v_size_2970_);
lean_ctor_set(v_reuseFailAlloc_3112_, 7, v_idx_2975_);
lean_ctor_set(v_reuseFailAlloc_3112_, 8, v_generation_2976_);
lean_ctor_set(v_reuseFailAlloc_3112_, 9, v_mt_2977_);
lean_ctor_set(v_reuseFailAlloc_3112_, 10, v_sTerms_2978_);
lean_ctor_set(v_reuseFailAlloc_3112_, 11, v_ematchDiagSource_2980_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*12, v_flipped_2969_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*12 + 1, v_interpreted_2971_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*12 + 2, v_ctor_2972_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*12 + 3, v_hasLambdas_2973_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*12 + 4, v_heqProofs_2974_);
lean_ctor_set_uint8(v_reuseFailAlloc_3112_, sizeof(void*)*12 + 5, v_funCC_2979_);
v___x_3011_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3010_;
}
v___jp_2985_:
{
size_t v___x_2986_; size_t v___x_2987_; uint8_t v___x_2988_; 
v___x_2986_ = lean_ptr_addr(v_next_2965_);
v___x_2987_ = lean_ptr_addr(v_lhs_2943_);
v___x_2988_ = lean_usize_dec_eq(v___x_2986_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2990_; 
lean_del_object(v___x_2962_);
lean_dec(v_snd_2955_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v_next_2965_);
lean_ctor_set(v___x_2957_, 0, v___x_2984_);
v___x_2990_ = v___x_2957_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2984_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_next_2965_);
v___x_2990_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
v_a_2946_ = v___x_2990_;
goto _start;
}
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_rootNew_2944_);
v___x_2993_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 0, v___x_2993_);
v___x_2995_ = v___x_2957_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_snd_2955_);
v___x_2995_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2997_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_2995_);
v___x_2997_ = v___x_2962_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
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
v___jp_3000_:
{
if (lean_obj_tag(v___y_3001_) == 0)
{
lean_dec_ref_known(v___y_3001_, 1);
goto v___jp_2985_;
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec_ref(v_next_2965_);
lean_del_object(v___x_2962_);
lean_del_object(v___x_2957_);
lean_dec(v_snd_2955_);
lean_dec_ref(v_rootNew_2944_);
v_a_3002_ = lean_ctor_get(v___y_3001_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___y_3001_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___y_3001_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___y_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
v_reusejp_3010_:
{
lean_object* v___x_3012_; 
lean_inc_ref(v___x_3011_);
lean_inc_ref(v_self_2964_);
v___x_3012_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2964_, v___x_3011_, v___y_2947_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_dec_ref_known(v___x_3012_, 1);
if (v_a_2945_ == 0)
{
lean_dec_ref(v___x_3011_);
lean_dec(v_ematchDiagSource_2980_);
lean_dec(v_sTerms_2978_);
lean_dec(v_mt_2977_);
lean_dec(v_generation_2976_);
lean_dec(v_idx_2975_);
lean_dec(v_size_2970_);
lean_dec(v_proof_x3f_2968_);
lean_dec(v_target_x3f_2967_);
lean_dec_ref(v_self_2964_);
goto v___jp_2985_;
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3013_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_3014_ = lean_unsigned_to_nat(3u);
v___x_3015_ = l_Lean_Expr_isAppOfArity(v_self_2964_, v___x_3013_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_dec_ref(v___x_3011_);
lean_dec(v_ematchDiagSource_2980_);
lean_dec(v_sTerms_2978_);
lean_dec(v_mt_2977_);
lean_dec(v_generation_2976_);
lean_dec(v_idx_2975_);
lean_dec(v_size_2970_);
lean_dec(v_proof_x3f_2968_);
lean_dec(v_target_x3f_2967_);
lean_dec_ref(v_self_2964_);
goto v___jp_2985_;
}
else
{
uint8_t v___x_3016_; 
v___x_3016_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_3011_);
lean_dec_ref(v___x_3011_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; lean_object* v_toGoalState_3018_; lean_object* v_enodeMap_3019_; lean_object* v_congrTable_3020_; lean_object* v___x_3021_; 
v___x_3017_ = lean_st_ref_get(v___y_2947_);
v_toGoalState_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc_ref(v_toGoalState_3018_);
lean_dec(v___x_3017_);
v_enodeMap_3019_ = lean_ctor_get(v_toGoalState_3018_, 1);
lean_inc_ref(v_enodeMap_3019_);
v_congrTable_3020_ = lean_ctor_get(v_toGoalState_3018_, 4);
lean_inc_ref(v_congrTable_3020_);
lean_dec_ref(v_toGoalState_3018_);
lean_inc_ref(v_self_2964_);
v___x_3021_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3019_, v_congrTable_3020_, v_self_2964_);
lean_dec_ref(v_congrTable_3020_);
lean_dec_ref(v_enodeMap_3019_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_dec(v_ematchDiagSource_2980_);
lean_dec(v_sTerms_2978_);
lean_dec(v_mt_2977_);
lean_dec(v_generation_2976_);
lean_dec(v_idx_2975_);
lean_dec(v_size_2970_);
lean_dec(v_proof_x3f_2968_);
lean_dec(v_target_x3f_2967_);
lean_dec_ref(v_self_2964_);
goto v___jp_2985_;
}
else
{
lean_object* v_val_3022_; lean_object* v_fst_3023_; lean_object* v___x_3024_; 
v_val_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_val_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v_fst_3023_ = lean_ctor_get(v_val_3022_, 0);
lean_inc(v_fst_3023_);
lean_dec(v_val_3022_);
v___x_3024_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3023_, v___y_2948_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; uint8_t v___x_3026_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = lean_unbox(v_a_3025_);
lean_dec(v_a_3025_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; lean_object* v_toGoalState_3028_; lean_object* v_mvarId_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3103_; 
v___x_3027_ = lean_st_ref_take(v___y_2947_);
v_toGoalState_3028_ = lean_ctor_get(v___x_3027_, 0);
v_mvarId_3029_ = lean_ctor_get(v___x_3027_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3031_ = v___x_3027_;
v_isShared_3032_ = v_isSharedCheck_3103_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_mvarId_3029_);
lean_inc(v_toGoalState_3028_);
lean_dec(v___x_3027_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3103_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v_nextDeclIdx_3033_; lean_object* v_enodeMap_3034_; lean_object* v_exprs_3035_; lean_object* v_parents_3036_; lean_object* v_congrTable_3037_; lean_object* v_appMap_3038_; lean_object* v_indicesFound_3039_; lean_object* v_newFacts_3040_; uint8_t v_inconsistent_3041_; lean_object* v_nextIdx_3042_; lean_object* v_newRawFacts_3043_; lean_object* v_facts_3044_; lean_object* v_extThms_3045_; lean_object* v_ematch_3046_; lean_object* v_inj_3047_; lean_object* v_split_3048_; lean_object* v_clean_3049_; lean_object* v_sstates_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3102_; 
v_nextDeclIdx_3033_ = lean_ctor_get(v_toGoalState_3028_, 0);
v_enodeMap_3034_ = lean_ctor_get(v_toGoalState_3028_, 1);
v_exprs_3035_ = lean_ctor_get(v_toGoalState_3028_, 2);
v_parents_3036_ = lean_ctor_get(v_toGoalState_3028_, 3);
v_congrTable_3037_ = lean_ctor_get(v_toGoalState_3028_, 4);
v_appMap_3038_ = lean_ctor_get(v_toGoalState_3028_, 5);
v_indicesFound_3039_ = lean_ctor_get(v_toGoalState_3028_, 6);
v_newFacts_3040_ = lean_ctor_get(v_toGoalState_3028_, 7);
v_inconsistent_3041_ = lean_ctor_get_uint8(v_toGoalState_3028_, sizeof(void*)*17);
v_nextIdx_3042_ = lean_ctor_get(v_toGoalState_3028_, 8);
v_newRawFacts_3043_ = lean_ctor_get(v_toGoalState_3028_, 9);
v_facts_3044_ = lean_ctor_get(v_toGoalState_3028_, 10);
v_extThms_3045_ = lean_ctor_get(v_toGoalState_3028_, 11);
v_ematch_3046_ = lean_ctor_get(v_toGoalState_3028_, 12);
v_inj_3047_ = lean_ctor_get(v_toGoalState_3028_, 13);
v_split_3048_ = lean_ctor_get(v_toGoalState_3028_, 14);
v_clean_3049_ = lean_ctor_get(v_toGoalState_3028_, 15);
v_sstates_3050_ = lean_ctor_get(v_toGoalState_3028_, 16);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_toGoalState_3028_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3052_ = v_toGoalState_3028_;
v_isShared_3053_ = v_isSharedCheck_3102_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_sstates_3050_);
lean_inc(v_clean_3049_);
lean_inc(v_split_3048_);
lean_inc(v_inj_3047_);
lean_inc(v_ematch_3046_);
lean_inc(v_extThms_3045_);
lean_inc(v_facts_3044_);
lean_inc(v_newRawFacts_3043_);
lean_inc(v_nextIdx_3042_);
lean_inc(v_newFacts_3040_);
lean_inc(v_indicesFound_3039_);
lean_inc(v_appMap_3038_);
lean_inc(v_congrTable_3037_);
lean_inc(v_parents_3036_);
lean_inc(v_exprs_3035_);
lean_inc(v_enodeMap_3034_);
lean_inc(v_nextDeclIdx_3033_);
lean_dec(v_toGoalState_3028_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3102_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v___x_3054_ = lean_box(0);
lean_inc_ref(v_self_2964_);
v___x_3055_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3034_, v_congrTable_3037_, v_self_2964_, v___x_3054_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 4, v___x_3055_);
v___x_3057_ = v___x_3052_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_nextDeclIdx_3033_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_enodeMap_3034_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_exprs_3035_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v_parents_3036_);
lean_ctor_set(v_reuseFailAlloc_3101_, 4, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3101_, 5, v_appMap_3038_);
lean_ctor_set(v_reuseFailAlloc_3101_, 6, v_indicesFound_3039_);
lean_ctor_set(v_reuseFailAlloc_3101_, 7, v_newFacts_3040_);
lean_ctor_set(v_reuseFailAlloc_3101_, 8, v_nextIdx_3042_);
lean_ctor_set(v_reuseFailAlloc_3101_, 9, v_newRawFacts_3043_);
lean_ctor_set(v_reuseFailAlloc_3101_, 10, v_facts_3044_);
lean_ctor_set(v_reuseFailAlloc_3101_, 11, v_extThms_3045_);
lean_ctor_set(v_reuseFailAlloc_3101_, 12, v_ematch_3046_);
lean_ctor_set(v_reuseFailAlloc_3101_, 13, v_inj_3047_);
lean_ctor_set(v_reuseFailAlloc_3101_, 14, v_split_3048_);
lean_ctor_set(v_reuseFailAlloc_3101_, 15, v_clean_3049_);
lean_ctor_set(v_reuseFailAlloc_3101_, 16, v_sstates_3050_);
lean_ctor_set_uint8(v_reuseFailAlloc_3101_, sizeof(void*)*17, v_inconsistent_3041_);
v___x_3057_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3059_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3057_);
v___x_3059_ = v___x_3031_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_mvarId_3029_);
v___x_3059_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = lean_st_ref_put(v___y_2947_, v___x_3059_);
lean_inc_ref(v_rootNew_2944_);
lean_inc_ref(v_next_2965_);
lean_inc_ref_n(v_self_2964_, 3);
v___x_3061_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3061_, 0, v_self_2964_);
lean_ctor_set(v___x_3061_, 1, v_next_2965_);
lean_ctor_set(v___x_3061_, 2, v_rootNew_2944_);
lean_ctor_set(v___x_3061_, 3, v_self_2964_);
lean_ctor_set(v___x_3061_, 4, v_target_x3f_2967_);
lean_ctor_set(v___x_3061_, 5, v_proof_x3f_2968_);
lean_ctor_set(v___x_3061_, 6, v_size_2970_);
lean_ctor_set(v___x_3061_, 7, v_idx_2975_);
lean_ctor_set(v___x_3061_, 8, v_generation_2976_);
lean_ctor_set(v___x_3061_, 9, v_mt_2977_);
lean_ctor_set(v___x_3061_, 10, v_sTerms_2978_);
lean_ctor_set(v___x_3061_, 11, v_ematchDiagSource_2980_);
lean_ctor_set_uint8(v___x_3061_, sizeof(void*)*12, v_flipped_2969_);
lean_ctor_set_uint8(v___x_3061_, sizeof(void*)*12 + 1, v_interpreted_2971_);
lean_ctor_set_uint8(v___x_3061_, sizeof(void*)*12 + 2, v_ctor_2972_);
lean_ctor_set_uint8(v___x_3061_, sizeof(void*)*12 + 3, v_hasLambdas_2973_);
lean_ctor_set_uint8(v___x_3061_, sizeof(void*)*12 + 4, v_heqProofs_2974_);
lean_ctor_set_uint8(v___x_3061_, sizeof(void*)*12 + 5, v_funCC_2979_);
v___x_3062_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2964_, v___x_3061_, v___y_2947_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_dec_ref_known(v___x_3062_, 1);
v___x_3063_ = lean_st_ref_get(v___y_2947_);
lean_inc(v_fst_3023_);
v___x_3064_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3063_, v_fst_3023_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___x_3063_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v_self_3066_; lean_object* v_next_3067_; lean_object* v_root_3068_; lean_object* v_target_x3f_3069_; lean_object* v_proof_x3f_3070_; uint8_t v_flipped_3071_; lean_object* v_size_3072_; uint8_t v_interpreted_3073_; uint8_t v_ctor_3074_; uint8_t v_hasLambdas_3075_; uint8_t v_heqProofs_3076_; lean_object* v_idx_3077_; lean_object* v_generation_3078_; lean_object* v_mt_3079_; lean_object* v_sTerms_3080_; uint8_t v_funCC_3081_; lean_object* v_ematchDiagSource_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3090_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v_self_3066_ = lean_ctor_get(v_a_3065_, 0);
v_next_3067_ = lean_ctor_get(v_a_3065_, 1);
v_root_3068_ = lean_ctor_get(v_a_3065_, 2);
v_target_x3f_3069_ = lean_ctor_get(v_a_3065_, 4);
v_proof_x3f_3070_ = lean_ctor_get(v_a_3065_, 5);
v_flipped_3071_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*12);
v_size_3072_ = lean_ctor_get(v_a_3065_, 6);
v_interpreted_3073_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*12 + 1);
v_ctor_3074_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*12 + 2);
v_hasLambdas_3075_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*12 + 3);
v_heqProofs_3076_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*12 + 4);
v_idx_3077_ = lean_ctor_get(v_a_3065_, 7);
v_generation_3078_ = lean_ctor_get(v_a_3065_, 8);
v_mt_3079_ = lean_ctor_get(v_a_3065_, 9);
v_sTerms_3080_ = lean_ctor_get(v_a_3065_, 10);
v_funCC_3081_ = lean_ctor_get_uint8(v_a_3065_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3082_ = lean_ctor_get(v_a_3065_, 11);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_a_3065_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v_a_3065_, 3);
lean_dec(v_unused_3091_);
v___x_3084_ = v_a_3065_;
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_ematchDiagSource_3082_);
lean_inc(v_sTerms_3080_);
lean_inc(v_mt_3079_);
lean_inc(v_generation_3078_);
lean_inc(v_idx_3077_);
lean_inc(v_size_3072_);
lean_inc(v_proof_x3f_3070_);
lean_inc(v_target_x3f_3069_);
lean_inc(v_root_3068_);
lean_inc(v_next_3067_);
lean_inc(v_self_3066_);
lean_dec(v_a_3065_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3090_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 3, v_self_2964_);
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_self_3066_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_next_3067_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_root_3068_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_self_2964_);
lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_target_x3f_3069_);
lean_ctor_set(v_reuseFailAlloc_3089_, 5, v_proof_x3f_3070_);
lean_ctor_set(v_reuseFailAlloc_3089_, 6, v_size_3072_);
lean_ctor_set(v_reuseFailAlloc_3089_, 7, v_idx_3077_);
lean_ctor_set(v_reuseFailAlloc_3089_, 8, v_generation_3078_);
lean_ctor_set(v_reuseFailAlloc_3089_, 9, v_mt_3079_);
lean_ctor_set(v_reuseFailAlloc_3089_, 10, v_sTerms_3080_);
lean_ctor_set(v_reuseFailAlloc_3089_, 11, v_ematchDiagSource_3082_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*12, v_flipped_3071_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*12 + 1, v_interpreted_3073_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*12 + 2, v_ctor_3074_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*12 + 3, v_hasLambdas_3075_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*12 + 4, v_heqProofs_3076_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*12 + 5, v_funCC_3081_);
v___x_3087_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3023_, v___x_3087_, v___y_2947_);
v___y_3001_ = v___x_3088_;
goto v___jp_3000_;
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_fst_3023_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_self_2964_);
lean_del_object(v___x_2962_);
lean_del_object(v___x_2957_);
lean_dec(v_snd_2955_);
lean_dec_ref(v_rootNew_2944_);
v_a_3092_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3064_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3064_);
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
else
{
lean_dec(v_fst_3023_);
lean_dec_ref(v_self_2964_);
v___y_3001_ = v___x_3062_;
goto v___jp_3000_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3023_);
lean_dec(v_ematchDiagSource_2980_);
lean_dec(v_sTerms_2978_);
lean_dec(v_mt_2977_);
lean_dec(v_generation_2976_);
lean_dec(v_idx_2975_);
lean_dec(v_size_2970_);
lean_dec(v_proof_x3f_2968_);
lean_dec(v_target_x3f_2967_);
lean_dec_ref(v_self_2964_);
goto v___jp_2985_;
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_fst_3023_);
lean_dec(v_ematchDiagSource_2980_);
lean_dec(v_sTerms_2978_);
lean_dec(v_mt_2977_);
lean_dec(v_generation_2976_);
lean_dec(v_idx_2975_);
lean_dec(v_size_2970_);
lean_dec(v_proof_x3f_2968_);
lean_dec(v_target_x3f_2967_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_self_2964_);
lean_del_object(v___x_2962_);
lean_del_object(v___x_2957_);
lean_dec(v_snd_2955_);
lean_dec_ref(v_rootNew_2944_);
v_a_3104_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3024_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3024_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2980_);
lean_dec(v_sTerms_2978_);
lean_dec(v_mt_2977_);
lean_dec(v_generation_2976_);
lean_dec(v_idx_2975_);
lean_dec(v_size_2970_);
lean_dec(v_proof_x3f_2968_);
lean_dec(v_target_x3f_2967_);
lean_dec_ref(v_self_2964_);
goto v___jp_2985_;
}
}
}
}
else
{
lean_dec_ref(v___x_3011_);
lean_dec(v_ematchDiagSource_2980_);
lean_dec(v_sTerms_2978_);
lean_dec(v_mt_2977_);
lean_dec(v_generation_2976_);
lean_dec(v_idx_2975_);
lean_dec(v_size_2970_);
lean_dec(v_proof_x3f_2968_);
lean_dec(v_target_x3f_2967_);
lean_dec_ref(v_self_2964_);
v___y_3001_ = v___x_3012_;
goto v___jp_3000_;
}
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_del_object(v___x_2957_);
lean_dec(v_snd_2955_);
lean_dec_ref(v_rootNew_2944_);
v_a_3116_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_2959_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_2959_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3126_, lean_object* v_rootNew_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
uint8_t v_a_26281__boxed_3137_; lean_object* v_res_3138_; 
v_a_26281__boxed_3137_ = lean_unbox(v_a_3128_);
v_res_3138_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3126_, v_rootNew_3127_, v_a_26281__boxed_3137_, v_a_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v_lhs_3126_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3139_, lean_object* v_rootNew_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3140_, v_a_3145_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___x_3152_, 1);
v___x_3154_ = lean_box(0);
lean_inc_ref(v_lhs_3139_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
lean_ctor_set(v___x_3155_, 1, v_lhs_3139_);
v___x_3156_ = lean_unbox(v_a_3153_);
lean_dec(v_a_3153_);
v___x_3157_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3139_, v_rootNew_3140_, v___x_3156_, v___x_3155_, v_a_3141_, v_a_3145_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_);
lean_dec_ref(v_lhs_3139_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3171_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3171_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3171_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_fst_3162_; 
v_fst_3162_ = lean_ctor_get(v_a_3158_, 0);
lean_inc(v_fst_3162_);
lean_dec(v_a_3158_);
if (lean_obj_tag(v_fst_3162_) == 0)
{
lean_object* v___x_3163_; lean_object* v___x_3165_; 
v___x_3163_ = lean_box(0);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3163_);
v___x_3165_ = v___x_3160_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3163_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
else
{
lean_object* v_val_3167_; lean_object* v___x_3169_; 
v_val_3167_ = lean_ctor_get(v_fst_3162_, 0);
lean_inc(v_val_3167_);
lean_dec_ref_known(v_fst_3162_, 1);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v_val_3167_);
v___x_3169_ = v___x_3160_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_val_3167_);
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
v_a_3172_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3157_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3157_);
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
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec_ref(v_rootNew_3140_);
lean_dec_ref(v_lhs_3139_);
v_a_3180_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3152_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3152_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3188_, lean_object* v_rootNew_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3188_, v_rootNew_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_);
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3198_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec(v_a_3190_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3202_, lean_object* v_00_u03b2_3203_, lean_object* v_x_3204_, lean_object* v_x_3205_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3202_, v_x_3204_, v_x_3205_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3207_, lean_object* v_00_u03b2_3208_, lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3207_, v_00_u03b2_3208_, v_x_3209_, v_x_3210_);
lean_dec_ref(v_x_3209_);
lean_dec_ref(v___x_3207_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3212_, lean_object* v_00_u03b2_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_, lean_object* v_x_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3212_, v_x_3214_, v_x_3215_, v_x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3218_, lean_object* v_00_u03b2_3219_, lean_object* v_x_3220_, lean_object* v_x_3221_, lean_object* v_x_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3218_, v_00_u03b2_3219_, v_x_3220_, v_x_3221_, v_x_3222_);
lean_dec_ref(v___x_3218_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3224_, lean_object* v_rootNew_3225_, uint8_t v_a_3226_, lean_object* v_inst_3227_, lean_object* v_a_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3224_, v_rootNew_3225_, v_a_3226_, v_a_3228_, v___y_3229_, v___y_3233_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3241_, lean_object* v_rootNew_3242_, lean_object* v_a_3243_, lean_object* v_inst_3244_, lean_object* v_a_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v_a_26640__boxed_3257_; lean_object* v_res_3258_; 
v_a_26640__boxed_3257_ = lean_unbox(v_a_3243_);
v_res_3258_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3241_, v_rootNew_3242_, v_a_26640__boxed_3257_, v_inst_3244_, v_a_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
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
lean_dec_ref(v_lhs_3241_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3259_, lean_object* v_00_u03b2_3260_, lean_object* v_x_3261_, size_t v_x_3262_, lean_object* v_x_3263_){
_start:
{
lean_object* v___x_3264_; 
lean_inc_ref(v_x_3261_);
v___x_3264_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3259_, v_x_3261_, v_x_3262_, v_x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3265_, lean_object* v_00_u03b2_3266_, lean_object* v_x_3267_, lean_object* v_x_3268_, lean_object* v_x_3269_){
_start:
{
size_t v_x_26683__boxed_3270_; lean_object* v_res_3271_; 
v_x_26683__boxed_3270_ = lean_unbox_usize(v_x_3268_);
lean_dec(v_x_3268_);
v_res_3271_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3265_, v_00_u03b2_3266_, v_x_3267_, v_x_26683__boxed_3270_, v_x_3269_);
lean_dec_ref(v_x_3267_);
lean_dec_ref(v___x_3265_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3272_, lean_object* v_00_u03b2_3273_, lean_object* v_x_3274_, size_t v_x_3275_, size_t v_x_3276_, lean_object* v_x_3277_, lean_object* v_x_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3272_, v_x_3274_, v_x_3275_, v_x_3276_, v_x_3277_, v_x_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3280_, lean_object* v_00_u03b2_3281_, lean_object* v_x_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_){
_start:
{
size_t v_x_26697__boxed_3287_; size_t v_x_26698__boxed_3288_; lean_object* v_res_3289_; 
v_x_26697__boxed_3287_ = lean_unbox_usize(v_x_3283_);
lean_dec(v_x_3283_);
v_x_26698__boxed_3288_ = lean_unbox_usize(v_x_3284_);
lean_dec(v_x_3284_);
v_res_3289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3280_, v_00_u03b2_3281_, v_x_3282_, v_x_26697__boxed_3287_, v_x_26698__boxed_3288_, v_x_3285_, v_x_3286_);
lean_dec_ref(v___x_3280_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3290_, lean_object* v_00_u03b2_3291_, lean_object* v_keys_3292_, lean_object* v_vals_3293_, lean_object* v_heq_3294_, lean_object* v_i_3295_, lean_object* v_k_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3290_, v_keys_3292_, v_vals_3293_, v_i_3295_, v_k_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3298_, lean_object* v_00_u03b2_3299_, lean_object* v_keys_3300_, lean_object* v_vals_3301_, lean_object* v_heq_3302_, lean_object* v_i_3303_, lean_object* v_k_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3298_, v_00_u03b2_3299_, v_keys_3300_, v_vals_3301_, v_heq_3302_, v_i_3303_, v_k_3304_);
lean_dec_ref(v_vals_3301_);
lean_dec_ref(v_keys_3300_);
lean_dec_ref(v___x_3298_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3306_, lean_object* v_00_u03b2_3307_, lean_object* v_n_3308_, lean_object* v_k_3309_, lean_object* v_v_3310_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3306_, v_n_3308_, v_k_3309_, v_v_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3312_, lean_object* v_00_u03b2_3313_, lean_object* v_n_3314_, lean_object* v_k_3315_, lean_object* v_v_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3312_, v_00_u03b2_3313_, v_n_3314_, v_k_3315_, v_v_3316_);
lean_dec_ref(v___x_3312_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3318_, lean_object* v_00_u03b2_3319_, size_t v_depth_3320_, lean_object* v_keys_3321_, lean_object* v_vals_3322_, lean_object* v_heq_3323_, lean_object* v_i_3324_, lean_object* v_entries_3325_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3318_, v_depth_3320_, v_keys_3321_, v_vals_3322_, v_i_3324_, v_entries_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3327_, lean_object* v_00_u03b2_3328_, lean_object* v_depth_3329_, lean_object* v_keys_3330_, lean_object* v_vals_3331_, lean_object* v_heq_3332_, lean_object* v_i_3333_, lean_object* v_entries_3334_){
_start:
{
size_t v_depth_boxed_3335_; lean_object* v_res_3336_; 
v_depth_boxed_3335_ = lean_unbox_usize(v_depth_3329_);
lean_dec(v_depth_3329_);
v_res_3336_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3327_, v_00_u03b2_3328_, v_depth_boxed_3335_, v_keys_3330_, v_vals_3331_, v_heq_3332_, v_i_3333_, v_entries_3334_);
lean_dec_ref(v_vals_3331_);
lean_dec_ref(v_keys_3330_);
lean_dec_ref(v___x_3327_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3337_, lean_object* v_00_u03b2_3338_, lean_object* v_x_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_, lean_object* v_x_3342_){
_start:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3337_, v_x_3339_, v_x_3340_, v_x_3341_, v_x_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3344_, lean_object* v_00_u03b2_3345_, lean_object* v_x_3346_, lean_object* v_x_3347_, lean_object* v_x_3348_, lean_object* v_x_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3344_, v_00_u03b2_3345_, v_x_3346_, v_x_3347_, v_x_3348_, v_x_3349_);
lean_dec_ref(v___x_3344_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3351_, lean_object* v_b_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
if (lean_obj_tag(v_as_x27_3351_) == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v_b_3352_);
return v___x_3364_;
}
else
{
lean_object* v_head_3365_; lean_object* v_tail_3366_; lean_object* v___x_3367_; 
v_head_3365_ = lean_ctor_get(v_as_x27_3351_, 0);
v_tail_3366_ = lean_ctor_get(v_as_x27_3351_, 1);
lean_inc(v_head_3365_);
v___x_3367_ = l_Lean_Meta_Grind_propagateUp(v_head_3365_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v___x_3368_; 
lean_dec_ref_known(v___x_3367_, 1);
v___x_3368_ = lean_box(0);
v_as_x27_3351_ = v_tail_3366_;
v_b_3352_ = v___x_3368_;
goto _start;
}
else
{
return v___x_3367_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3370_, lean_object* v_b_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3370_, v_b_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec(v_as_x27_3370_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3384_, lean_object* v_b_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
if (lean_obj_tag(v_as_x27_3384_) == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3397_, 0, v_b_3385_);
return v___x_3397_;
}
else
{
lean_object* v_head_3398_; lean_object* v_tail_3399_; lean_object* v___x_3400_; 
v_head_3398_ = lean_ctor_get(v_as_x27_3384_, 0);
v_tail_3399_ = lean_ctor_get(v_as_x27_3384_, 1);
lean_inc(v_head_3398_);
v___x_3400_ = l_Lean_Meta_Grind_propagateDown(v_head_3398_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v___x_3401_; 
lean_dec_ref_known(v___x_3400_, 1);
v___x_3401_ = lean_box(0);
v_as_x27_3384_ = v_tail_3399_;
v_b_3385_ = v___x_3401_;
goto _start;
}
else
{
return v___x_3400_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3403_, lean_object* v_b_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3403_, v_b_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec(v_as_x27_3403_);
return v_res_3416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_cls_3420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3421_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3422_ = l_Lean_Name_append(v___x_3421_, v_cls_3420_);
return v___x_3422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3425_ = l_Lean_stringToMessageData(v___x_3424_);
return v___x_3425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3435_, uint8_t v_isHEq_3436_, lean_object* v_lhs_3437_, lean_object* v_rhs_3438_, lean_object* v_lhsNode_3439_, lean_object* v_rhsNode_3440_, lean_object* v_lhsRoot_3441_, lean_object* v_rhsRoot_3442_, uint8_t v_flipped_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3508_; lean_object* v___y_3509_; uint8_t v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; uint8_t v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; uint8_t v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; uint8_t v___y_3541_; lean_object* v___y_3542_; uint8_t v___y_3543_; lean_object* v___y_3573_; lean_object* v___y_3574_; uint8_t v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; uint8_t v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; uint8_t v___y_3591_; uint8_t v___y_3592_; lean_object* v___y_3593_; uint8_t v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; uint8_t v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; uint8_t v___y_3609_; lean_object* v___y_3611_; lean_object* v___y_3612_; uint8_t v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; uint8_t v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v_options_3693_; lean_object* v_toCold_3694_; uint8_t v_hasTrace_3695_; lean_object* v_cls_3696_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v_fns_u2082_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v_fns_u2081_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; 
v_options_3693_ = lean_ctor_get(v_a_3452_, 1);
v_toCold_3694_ = lean_ctor_get(v_a_3452_, 0);
v_hasTrace_3695_ = lean_ctor_get_uint8(v_options_3693_, sizeof(void*)*1);
v_cls_3696_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3695_ == 0)
{
v___y_3816_ = v_a_3444_;
v___y_3817_ = v_a_3445_;
v___y_3818_ = v_a_3446_;
v___y_3819_ = v_a_3447_;
v___y_3820_ = v_a_3448_;
v___y_3821_ = v_a_3449_;
v___y_3822_ = v_a_3450_;
v___y_3823_ = v_a_3451_;
v___y_3824_ = v_a_3452_;
v___y_3825_ = v_a_3453_;
goto v___jp_3815_;
}
else
{
lean_object* v_inheritedTraceOptions_3896_; lean_object* v___x_3897_; uint8_t v___x_3898_; 
v_inheritedTraceOptions_3896_ = lean_ctor_get(v_toCold_3694_, 4);
v___x_3897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3898_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3896_, v_options_3693_, v___x_3897_);
if (v___x_3898_ == 0)
{
v___y_3816_ = v_a_3444_;
v___y_3817_ = v_a_3445_;
v___y_3818_ = v_a_3446_;
v___y_3819_ = v_a_3447_;
v___y_3820_ = v_a_3448_;
v___y_3821_ = v_a_3449_;
v___y_3822_ = v_a_3450_;
v___y_3823_ = v_a_3451_;
v___y_3824_ = v_a_3452_;
v___y_3825_ = v_a_3453_;
goto v___jp_3815_;
}
else
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Meta_Grind_updateLastTag(v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v___x_3900_; 
lean_dec_ref_known(v___x_3899_, 1);
lean_inc_ref(v_lhs_3437_);
v___x_3900_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3437_, v_a_3444_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3902_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3900_, 1);
lean_inc_ref(v_rhs_3438_);
v___x_3902_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3438_, v_a_3444_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3902_, 1);
v___x_3904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
lean_ctor_set(v___x_3905_, 1, v_a_3901_);
v___x_3906_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3905_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v_a_3903_);
v___x_3909_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3696_, v___x_3908_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_dec_ref_known(v___x_3909_, 1);
v___y_3816_ = v_a_3444_;
v___y_3817_ = v_a_3445_;
v___y_3818_ = v_a_3446_;
v___y_3819_ = v_a_3447_;
v___y_3820_ = v_a_3448_;
v___y_3821_ = v_a_3449_;
v___y_3822_ = v_a_3450_;
v___y_3823_ = v_a_3451_;
v___y_3824_ = v_a_3452_;
v___y_3825_ = v_a_3453_;
goto v___jp_3815_;
}
else
{
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhsNode_3439_);
lean_dec_ref(v_rhs_3438_);
lean_dec_ref(v_lhs_3437_);
lean_dec_ref(v_proof_3435_);
return v___x_3909_;
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_dec(v_a_3901_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhsNode_3439_);
lean_dec_ref(v_rhs_3438_);
lean_dec_ref(v_lhs_3437_);
lean_dec_ref(v_proof_3435_);
v_a_3910_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3902_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3902_);
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
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhsNode_3439_);
lean_dec_ref(v_rhs_3438_);
lean_dec_ref(v_lhs_3437_);
lean_dec_ref(v_proof_3435_);
v_a_3918_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3900_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3900_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhsNode_3439_);
lean_dec_ref(v_rhs_3438_);
lean_dec_ref(v_lhs_3437_);
lean_dec_ref(v_proof_3435_);
return v___x_3899_;
}
}
}
v___jp_3455_:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3462_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3498_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3498_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3498_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
uint8_t v___x_3477_; 
v___x_3477_ = lean_unbox(v_a_3473_);
lean_dec(v_a_3473_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_del_object(v___x_3475_);
v___x_3478_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3457_);
lean_dec(v___y_3457_);
v___x_3479_ = lean_box(0);
v___x_3480_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3478_, v___x_3479_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___x_3478_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v___x_3481_; 
lean_dec_ref_known(v___x_3480_, 1);
v___x_3481_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3456_, v___x_3479_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v___x_3482_; 
lean_dec_ref_known(v___x_3481_, 1);
v___x_3482_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3459_, v___y_3460_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v___x_3483_; 
lean_dec_ref_known(v___x_3482_, 1);
v___x_3483_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3458_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3492_; 
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3483_);
if (v_isSharedCheck_3492_ == 0)
{
lean_object* v_unused_3493_; 
v_unused_3493_ = lean_ctor_get(v___x_3483_, 0);
lean_dec(v_unused_3493_);
v___x_3485_ = v___x_3483_;
v_isShared_3486_ = v_isSharedCheck_3492_;
goto v_resetjp_3484_;
}
else
{
lean_dec(v___x_3483_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3492_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
uint8_t v___x_3487_; 
v___x_3487_ = l_Lean_Expr_isTrue(v___y_3461_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3489_; 
lean_dec(v___y_3456_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3479_);
v___x_3489_ = v___x_3485_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3479_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
else
{
lean_object* v___x_3491_; 
lean_del_object(v___x_3485_);
v___x_3491_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3456_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3456_);
return v___x_3491_;
}
}
}
else
{
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3456_);
return v___x_3483_;
}
}
else
{
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3458_);
lean_dec(v___y_3456_);
return v___x_3482_;
}
}
else
{
lean_dec_ref(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec(v___y_3456_);
return v___x_3481_;
}
}
else
{
lean_dec_ref(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec(v___y_3456_);
return v___x_3480_;
}
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3496_; 
lean_dec_ref(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
v___x_3494_ = lean_box(0);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3494_);
v___x_3496_ = v___x_3475_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3494_);
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
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec_ref(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
v_a_3499_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3472_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3472_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
v___jp_3507_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_inc_ref(v___y_3515_);
v___x_3544_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3544_, 0, v___y_3515_);
lean_ctor_set(v___x_3544_, 1, v___y_3519_);
lean_ctor_set(v___x_3544_, 2, v___y_3509_);
lean_ctor_set(v___x_3544_, 3, v___y_3524_);
lean_ctor_set(v___x_3544_, 4, v___y_3530_);
lean_ctor_set(v___x_3544_, 5, v___y_3528_);
lean_ctor_set(v___x_3544_, 6, v___y_3520_);
lean_ctor_set(v___x_3544_, 7, v___y_3508_);
lean_ctor_set(v___x_3544_, 8, v___y_3533_);
lean_ctor_set(v___x_3544_, 9, v___y_3525_);
lean_ctor_set(v___x_3544_, 10, v___y_3522_);
lean_ctor_set(v___x_3544_, 11, v___y_3532_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12, v___y_3534_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12 + 1, v___y_3513_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12 + 2, v___y_3510_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12 + 3, v___y_3541_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12 + 4, v___y_3543_);
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*12 + 5, v___y_3526_);
lean_inc_ref(v___y_3535_);
v___x_3545_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3535_, v___x_3544_, v___y_3523_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v___x_3546_; 
lean_dec_ref_known(v___x_3545_, 1);
lean_inc_ref(v___y_3542_);
v___x_3546_ = l_Lean_Meta_Grind_propagateBeta(v___y_3542_, v___y_3518_, v___y_3523_, v___y_3521_, v___y_3540_, v___y_3514_, v___y_3527_, v___y_3517_, v___y_3537_, v___y_3512_, v___y_3536_, v___y_3529_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v___x_3547_; 
lean_dec_ref_known(v___x_3546_, 1);
lean_inc_ref(v___y_3516_);
v___x_3547_ = l_Lean_Meta_Grind_propagateBeta(v___y_3516_, v___y_3539_, v___y_3523_, v___y_3521_, v___y_3540_, v___y_3514_, v___y_3527_, v___y_3517_, v___y_3537_, v___y_3512_, v___y_3536_, v___y_3529_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v___x_3548_; 
lean_dec_ref_known(v___x_3547_, 1);
v___x_3548_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3442_, v_lhsRoot_3441_, v___y_3523_, v___y_3537_, v___y_3512_, v___y_3536_, v___y_3529_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3550_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3548_, 1);
v___x_3550_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3531_, v___y_3523_);
lean_dec_ref(v___y_3531_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3551_; 
lean_dec_ref_known(v___x_3550_, 1);
lean_inc_ref(v___y_3535_);
v___x_3551_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3511_, v___y_3535_, v___y_3523_, v___y_3521_, v___y_3540_, v___y_3514_, v___y_3527_, v___y_3517_, v___y_3537_, v___y_3512_, v___y_3536_, v___y_3529_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v___x_3552_; 
lean_dec_ref_known(v___x_3551_, 1);
v___x_3552_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3523_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; uint8_t v___x_3554_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3552_, 1);
v___x_3554_ = lean_unbox(v_a_3553_);
lean_dec(v_a_3553_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; 
v___x_3555_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3515_, v___y_3523_, v___y_3521_, v___y_3540_, v___y_3514_, v___y_3527_, v___y_3517_, v___y_3537_, v___y_3512_, v___y_3536_, v___y_3529_);
lean_dec_ref(v___y_3515_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_dec_ref_known(v___x_3555_, 1);
v___y_3456_ = v___y_3538_;
v___y_3457_ = v___y_3511_;
v___y_3458_ = v_a_3549_;
v___y_3459_ = v___y_3542_;
v___y_3460_ = v___y_3516_;
v___y_3461_ = v___y_3535_;
v___y_3462_ = v___y_3523_;
v___y_3463_ = v___y_3521_;
v___y_3464_ = v___y_3540_;
v___y_3465_ = v___y_3514_;
v___y_3466_ = v___y_3527_;
v___y_3467_ = v___y_3517_;
v___y_3468_ = v___y_3537_;
v___y_3469_ = v___y_3512_;
v___y_3470_ = v___y_3536_;
v___y_3471_ = v___y_3529_;
goto v___jp_3455_;
}
else
{
lean_dec(v_a_3549_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3511_);
return v___x_3555_;
}
}
else
{
lean_dec_ref(v___y_3515_);
v___y_3456_ = v___y_3538_;
v___y_3457_ = v___y_3511_;
v___y_3458_ = v_a_3549_;
v___y_3459_ = v___y_3542_;
v___y_3460_ = v___y_3516_;
v___y_3461_ = v___y_3535_;
v___y_3462_ = v___y_3523_;
v___y_3463_ = v___y_3521_;
v___y_3464_ = v___y_3540_;
v___y_3465_ = v___y_3514_;
v___y_3466_ = v___y_3527_;
v___y_3467_ = v___y_3517_;
v___y_3468_ = v___y_3537_;
v___y_3469_ = v___y_3512_;
v___y_3470_ = v___y_3536_;
v___y_3471_ = v___y_3529_;
goto v___jp_3455_;
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec(v_a_3549_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
v_a_3556_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3552_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3552_);
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
lean_dec(v_a_3549_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
return v___x_3551_;
}
}
else
{
lean_dec(v_a_3549_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
return v___x_3550_;
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
v_a_3564_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3548_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3548_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
else
{
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
return v___x_3547_;
}
}
else
{
lean_dec_ref(v___y_3542_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
return v___x_3546_;
}
}
else
{
lean_dec_ref(v___y_3542_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v___y_3531_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3511_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
return v___x_3545_;
}
}
v___jp_3572_:
{
if (v_isHEq_3436_ == 0)
{
if (v___y_3591_ == 0)
{
v___y_3508_ = v___y_3574_;
v___y_3509_ = v___y_3573_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3577_;
v___y_3513_ = v___y_3578_;
v___y_3514_ = v___y_3579_;
v___y_3515_ = v___y_3580_;
v___y_3516_ = v___y_3581_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3582_;
v___y_3519_ = v___y_3584_;
v___y_3520_ = v___y_3585_;
v___y_3521_ = v___y_3586_;
v___y_3522_ = v___y_3587_;
v___y_3523_ = v___y_3588_;
v___y_3524_ = v___y_3589_;
v___y_3525_ = v___y_3590_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3593_;
v___y_3528_ = v___y_3595_;
v___y_3529_ = v___y_3596_;
v___y_3530_ = v___y_3597_;
v___y_3531_ = v___y_3598_;
v___y_3532_ = v___y_3599_;
v___y_3533_ = v___y_3601_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3602_;
v___y_3536_ = v___y_3604_;
v___y_3537_ = v___y_3603_;
v___y_3538_ = v___y_3605_;
v___y_3539_ = v___y_3607_;
v___y_3540_ = v___y_3606_;
v___y_3541_ = v___y_3609_;
v___y_3542_ = v___y_3608_;
v___y_3543_ = v___y_3594_;
goto v___jp_3507_;
}
else
{
v___y_3508_ = v___y_3574_;
v___y_3509_ = v___y_3573_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3577_;
v___y_3513_ = v___y_3578_;
v___y_3514_ = v___y_3579_;
v___y_3515_ = v___y_3580_;
v___y_3516_ = v___y_3581_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3582_;
v___y_3519_ = v___y_3584_;
v___y_3520_ = v___y_3585_;
v___y_3521_ = v___y_3586_;
v___y_3522_ = v___y_3587_;
v___y_3523_ = v___y_3588_;
v___y_3524_ = v___y_3589_;
v___y_3525_ = v___y_3590_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3593_;
v___y_3528_ = v___y_3595_;
v___y_3529_ = v___y_3596_;
v___y_3530_ = v___y_3597_;
v___y_3531_ = v___y_3598_;
v___y_3532_ = v___y_3599_;
v___y_3533_ = v___y_3601_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3602_;
v___y_3536_ = v___y_3604_;
v___y_3537_ = v___y_3603_;
v___y_3538_ = v___y_3605_;
v___y_3539_ = v___y_3607_;
v___y_3540_ = v___y_3606_;
v___y_3541_ = v___y_3609_;
v___y_3542_ = v___y_3608_;
v___y_3543_ = v___y_3591_;
goto v___jp_3507_;
}
}
else
{
v___y_3508_ = v___y_3574_;
v___y_3509_ = v___y_3573_;
v___y_3510_ = v___y_3575_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3577_;
v___y_3513_ = v___y_3578_;
v___y_3514_ = v___y_3579_;
v___y_3515_ = v___y_3580_;
v___y_3516_ = v___y_3581_;
v___y_3517_ = v___y_3583_;
v___y_3518_ = v___y_3582_;
v___y_3519_ = v___y_3584_;
v___y_3520_ = v___y_3585_;
v___y_3521_ = v___y_3586_;
v___y_3522_ = v___y_3587_;
v___y_3523_ = v___y_3588_;
v___y_3524_ = v___y_3589_;
v___y_3525_ = v___y_3590_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3593_;
v___y_3528_ = v___y_3595_;
v___y_3529_ = v___y_3596_;
v___y_3530_ = v___y_3597_;
v___y_3531_ = v___y_3598_;
v___y_3532_ = v___y_3599_;
v___y_3533_ = v___y_3601_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3602_;
v___y_3536_ = v___y_3604_;
v___y_3537_ = v___y_3603_;
v___y_3538_ = v___y_3605_;
v___y_3539_ = v___y_3607_;
v___y_3540_ = v___y_3606_;
v___y_3541_ = v___y_3609_;
v___y_3542_ = v___y_3608_;
v___y_3543_ = v_isHEq_3436_;
goto v___jp_3507_;
}
}
v___jp_3610_:
{
lean_object* v___x_3633_; 
v___x_3633_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3612_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_dec_ref_known(v___x_3633_, 1);
v___x_3634_ = lean_st_ref_get(v___y_3623_);
v___x_3635_ = lean_st_ref_get(v___y_3623_);
lean_inc_ref(v___y_3617_);
v___x_3636_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3635_, v___y_3617_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___x_3635_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v_self_3638_; lean_object* v_root_3639_; lean_object* v_congr_3640_; lean_object* v_target_x3f_3641_; lean_object* v_proof_x3f_3642_; uint8_t v_flipped_3643_; lean_object* v_size_3644_; uint8_t v_interpreted_3645_; uint8_t v_ctor_3646_; uint8_t v_hasLambdas_3647_; uint8_t v_heqProofs_3648_; lean_object* v_idx_3649_; lean_object* v_generation_3650_; lean_object* v_mt_3651_; lean_object* v_sTerms_3652_; uint8_t v_funCC_3653_; lean_object* v_ematchDiagSource_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3683_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v_self_3638_ = lean_ctor_get(v_a_3637_, 0);
v_root_3639_ = lean_ctor_get(v_a_3637_, 2);
v_congr_3640_ = lean_ctor_get(v_a_3637_, 3);
v_target_x3f_3641_ = lean_ctor_get(v_a_3637_, 4);
v_proof_x3f_3642_ = lean_ctor_get(v_a_3637_, 5);
v_flipped_3643_ = lean_ctor_get_uint8(v_a_3637_, sizeof(void*)*12);
v_size_3644_ = lean_ctor_get(v_a_3637_, 6);
v_interpreted_3645_ = lean_ctor_get_uint8(v_a_3637_, sizeof(void*)*12 + 1);
v_ctor_3646_ = lean_ctor_get_uint8(v_a_3637_, sizeof(void*)*12 + 2);
v_hasLambdas_3647_ = lean_ctor_get_uint8(v_a_3637_, sizeof(void*)*12 + 3);
v_heqProofs_3648_ = lean_ctor_get_uint8(v_a_3637_, sizeof(void*)*12 + 4);
v_idx_3649_ = lean_ctor_get(v_a_3637_, 7);
v_generation_3650_ = lean_ctor_get(v_a_3637_, 8);
v_mt_3651_ = lean_ctor_get(v_a_3637_, 9);
v_sTerms_3652_ = lean_ctor_get(v_a_3637_, 10);
v_funCC_3653_ = lean_ctor_get_uint8(v_a_3637_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3654_ = lean_ctor_get(v_a_3637_, 11);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_a_3637_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v_a_3637_, 1);
lean_dec(v_unused_3684_);
v___x_3656_ = v_a_3637_;
v_isShared_3657_ = v_isSharedCheck_3683_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_ematchDiagSource_3654_);
lean_inc(v_sTerms_3652_);
lean_inc(v_mt_3651_);
lean_inc(v_generation_3650_);
lean_inc(v_idx_3649_);
lean_inc(v_size_3644_);
lean_inc(v_proof_x3f_3642_);
lean_inc(v_target_x3f_3641_);
lean_inc(v_congr_3640_);
lean_inc(v_root_3639_);
lean_inc(v_self_3638_);
lean_dec(v_a_3637_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3683_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v_self_3658_; lean_object* v_next_3659_; lean_object* v_root_3660_; lean_object* v_congr_3661_; lean_object* v_target_x3f_3662_; lean_object* v_proof_x3f_3663_; uint8_t v_flipped_3664_; lean_object* v_size_3665_; uint8_t v_interpreted_3666_; uint8_t v_ctor_3667_; uint8_t v_hasLambdas_3668_; uint8_t v_heqProofs_3669_; lean_object* v_idx_3670_; lean_object* v_generation_3671_; lean_object* v_mt_3672_; lean_object* v_sTerms_3673_; uint8_t v_funCC_3674_; lean_object* v_ematchDiagSource_3675_; lean_object* v___x_3677_; 
v_self_3658_ = lean_ctor_get(v_rhsRoot_3442_, 0);
v_next_3659_ = lean_ctor_get(v_rhsRoot_3442_, 1);
v_root_3660_ = lean_ctor_get(v_rhsRoot_3442_, 2);
v_congr_3661_ = lean_ctor_get(v_rhsRoot_3442_, 3);
v_target_x3f_3662_ = lean_ctor_get(v_rhsRoot_3442_, 4);
v_proof_x3f_3663_ = lean_ctor_get(v_rhsRoot_3442_, 5);
v_flipped_3664_ = lean_ctor_get_uint8(v_rhsRoot_3442_, sizeof(void*)*12);
v_size_3665_ = lean_ctor_get(v_rhsRoot_3442_, 6);
v_interpreted_3666_ = lean_ctor_get_uint8(v_rhsRoot_3442_, sizeof(void*)*12 + 1);
v_ctor_3667_ = lean_ctor_get_uint8(v_rhsRoot_3442_, sizeof(void*)*12 + 2);
v_hasLambdas_3668_ = lean_ctor_get_uint8(v_rhsRoot_3442_, sizeof(void*)*12 + 3);
v_heqProofs_3669_ = lean_ctor_get_uint8(v_rhsRoot_3442_, sizeof(void*)*12 + 4);
v_idx_3670_ = lean_ctor_get(v_rhsRoot_3442_, 7);
v_generation_3671_ = lean_ctor_get(v_rhsRoot_3442_, 8);
v_mt_3672_ = lean_ctor_get(v_rhsRoot_3442_, 9);
v_sTerms_3673_ = lean_ctor_get(v_rhsRoot_3442_, 10);
v_funCC_3674_ = lean_ctor_get_uint8(v_rhsRoot_3442_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3675_ = lean_ctor_get(v_rhsRoot_3442_, 11);
lean_inc_ref(v_next_3659_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 1, v_next_3659_);
v___x_3677_ = v___x_3656_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_self_3638_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_next_3659_);
lean_ctor_set(v_reuseFailAlloc_3682_, 2, v_root_3639_);
lean_ctor_set(v_reuseFailAlloc_3682_, 3, v_congr_3640_);
lean_ctor_set(v_reuseFailAlloc_3682_, 4, v_target_x3f_3641_);
lean_ctor_set(v_reuseFailAlloc_3682_, 5, v_proof_x3f_3642_);
lean_ctor_set(v_reuseFailAlloc_3682_, 6, v_size_3644_);
lean_ctor_set(v_reuseFailAlloc_3682_, 7, v_idx_3649_);
lean_ctor_set(v_reuseFailAlloc_3682_, 8, v_generation_3650_);
lean_ctor_set(v_reuseFailAlloc_3682_, 9, v_mt_3651_);
lean_ctor_set(v_reuseFailAlloc_3682_, 10, v_sTerms_3652_);
lean_ctor_set(v_reuseFailAlloc_3682_, 11, v_ematchDiagSource_3654_);
lean_ctor_set_uint8(v_reuseFailAlloc_3682_, sizeof(void*)*12, v_flipped_3643_);
lean_ctor_set_uint8(v_reuseFailAlloc_3682_, sizeof(void*)*12 + 1, v_interpreted_3645_);
lean_ctor_set_uint8(v_reuseFailAlloc_3682_, sizeof(void*)*12 + 2, v_ctor_3646_);
lean_ctor_set_uint8(v_reuseFailAlloc_3682_, sizeof(void*)*12 + 3, v_hasLambdas_3647_);
lean_ctor_set_uint8(v_reuseFailAlloc_3682_, sizeof(void*)*12 + 4, v_heqProofs_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3682_, sizeof(void*)*12 + 5, v_funCC_3653_);
v___x_3677_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3615_, v___x_3677_, v___y_3623_);
if (lean_obj_tag(v___x_3678_) == 0)
{
uint8_t v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
lean_dec_ref_known(v___x_3678_, 1);
v___x_3679_ = 0;
v___x_3680_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3634_, v_lhs_3437_, v___x_3679_);
lean_dec(v___x_3634_);
v___x_3681_ = lean_nat_add(v_size_3665_, v___y_3616_);
lean_dec(v___y_3616_);
if (v_hasLambdas_3668_ == 0)
{
lean_inc(v_generation_3671_);
lean_inc(v_ematchDiagSource_3675_);
lean_inc(v_target_x3f_3662_);
lean_inc(v_proof_x3f_3663_);
lean_inc(v_mt_3672_);
lean_inc_ref(v_congr_3661_);
lean_inc(v_sTerms_3673_);
lean_inc_ref(v_self_3658_);
lean_inc(v_idx_3670_);
lean_inc_ref(v_root_3660_);
v___y_3573_ = v_root_3660_;
v___y_3574_ = v_idx_3670_;
v___y_3575_ = v_ctor_3667_;
v___y_3576_ = v___y_3612_;
v___y_3577_ = v___y_3630_;
v___y_3578_ = v_interpreted_3666_;
v___y_3579_ = v___y_3626_;
v___y_3580_ = v_self_3658_;
v___y_3581_ = v___y_3620_;
v___y_3582_ = v___y_3621_;
v___y_3583_ = v___y_3628_;
v___y_3584_ = v___y_3611_;
v___y_3585_ = v___x_3681_;
v___y_3586_ = v___y_3624_;
v___y_3587_ = v_sTerms_3673_;
v___y_3588_ = v___y_3623_;
v___y_3589_ = v_congr_3661_;
v___y_3590_ = v_mt_3672_;
v___y_3591_ = v_heqProofs_3669_;
v___y_3592_ = v_funCC_3674_;
v___y_3593_ = v___y_3627_;
v___y_3594_ = v___y_3613_;
v___y_3595_ = v_proof_x3f_3663_;
v___y_3596_ = v___y_3632_;
v___y_3597_ = v_target_x3f_3662_;
v___y_3598_ = v___y_3617_;
v___y_3599_ = v_ematchDiagSource_3675_;
v___y_3600_ = v_flipped_3664_;
v___y_3601_ = v_generation_3671_;
v___y_3602_ = v___y_3622_;
v___y_3603_ = v___y_3629_;
v___y_3604_ = v___y_3631_;
v___y_3605_ = v___x_3680_;
v___y_3606_ = v___y_3625_;
v___y_3607_ = v___y_3614_;
v___y_3608_ = v___y_3619_;
v___y_3609_ = v___y_3618_;
goto v___jp_3572_;
}
else
{
lean_inc(v_generation_3671_);
lean_inc(v_ematchDiagSource_3675_);
lean_inc(v_target_x3f_3662_);
lean_inc(v_proof_x3f_3663_);
lean_inc(v_mt_3672_);
lean_inc_ref(v_congr_3661_);
lean_inc(v_sTerms_3673_);
lean_inc_ref(v_self_3658_);
lean_inc(v_idx_3670_);
lean_inc_ref(v_root_3660_);
v___y_3573_ = v_root_3660_;
v___y_3574_ = v_idx_3670_;
v___y_3575_ = v_ctor_3667_;
v___y_3576_ = v___y_3612_;
v___y_3577_ = v___y_3630_;
v___y_3578_ = v_interpreted_3666_;
v___y_3579_ = v___y_3626_;
v___y_3580_ = v_self_3658_;
v___y_3581_ = v___y_3620_;
v___y_3582_ = v___y_3621_;
v___y_3583_ = v___y_3628_;
v___y_3584_ = v___y_3611_;
v___y_3585_ = v___x_3681_;
v___y_3586_ = v___y_3624_;
v___y_3587_ = v_sTerms_3673_;
v___y_3588_ = v___y_3623_;
v___y_3589_ = v_congr_3661_;
v___y_3590_ = v_mt_3672_;
v___y_3591_ = v_heqProofs_3669_;
v___y_3592_ = v_funCC_3674_;
v___y_3593_ = v___y_3627_;
v___y_3594_ = v___y_3613_;
v___y_3595_ = v_proof_x3f_3663_;
v___y_3596_ = v___y_3632_;
v___y_3597_ = v_target_x3f_3662_;
v___y_3598_ = v___y_3617_;
v___y_3599_ = v_ematchDiagSource_3675_;
v___y_3600_ = v_flipped_3664_;
v___y_3601_ = v_generation_3671_;
v___y_3602_ = v___y_3622_;
v___y_3603_ = v___y_3629_;
v___y_3604_ = v___y_3631_;
v___y_3605_ = v___x_3680_;
v___y_3606_ = v___y_3625_;
v___y_3607_ = v___y_3614_;
v___y_3608_ = v___y_3619_;
v___y_3609_ = v_hasLambdas_3668_;
goto v___jp_3572_;
}
}
else
{
lean_dec(v___x_3634_);
lean_dec_ref(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_lhs_3437_);
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v___x_3634_);
lean_dec_ref(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_lhs_3437_);
v_a_3685_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3636_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3636_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
else
{
lean_dec_ref(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_lhs_3437_);
return v___x_3633_;
}
}
v___jp_3697_:
{
lean_object* v_self_3713_; lean_object* v_next_3714_; lean_object* v_size_3715_; uint8_t v_hasLambdas_3716_; uint8_t v_heqProofs_3717_; lean_object* v___x_3718_; 
v_self_3713_ = lean_ctor_get(v_lhsRoot_3441_, 0);
v_next_3714_ = lean_ctor_get(v_lhsRoot_3441_, 1);
v_size_3715_ = lean_ctor_get(v_lhsRoot_3441_, 6);
v_hasLambdas_3716_ = lean_ctor_get_uint8(v_lhsRoot_3441_, sizeof(void*)*12 + 3);
v_heqProofs_3717_ = lean_ctor_get_uint8(v_lhsRoot_3441_, sizeof(void*)*12 + 4);
v___x_3718_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3713_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v_root_3720_; lean_object* v___x_3721_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v_root_3720_ = lean_ctor_get(v_rhsNode_3440_, 2);
lean_inc_ref_n(v_root_3720_, 2);
lean_dec_ref(v_rhsNode_3440_);
lean_inc_ref(v_lhs_3437_);
v___x_3721_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3437_, v_root_3720_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_options_3722_; uint8_t v_hasTrace_3723_; 
lean_dec_ref_known(v___x_3721_, 1);
v_options_3722_ = lean_ctor_get(v___y_3711_, 1);
v_hasTrace_3723_ = lean_ctor_get_uint8(v_options_3722_, sizeof(void*)*1);
if (v_hasTrace_3723_ == 0)
{
lean_inc_ref(v_self_3713_);
lean_inc(v_size_3715_);
lean_inc_ref(v_next_3714_);
v___y_3611_ = v_next_3714_;
v___y_3612_ = v_a_3719_;
v___y_3613_ = v_heqProofs_3717_;
v___y_3614_ = v_fns_u2082_3702_;
v___y_3615_ = v___y_3698_;
v___y_3616_ = v_size_3715_;
v___y_3617_ = v_self_3713_;
v___y_3618_ = v_hasLambdas_3716_;
v___y_3619_ = v___y_3699_;
v___y_3620_ = v___y_3700_;
v___y_3621_ = v___y_3701_;
v___y_3622_ = v_root_3720_;
v___y_3623_ = v___y_3703_;
v___y_3624_ = v___y_3704_;
v___y_3625_ = v___y_3705_;
v___y_3626_ = v___y_3706_;
v___y_3627_ = v___y_3707_;
v___y_3628_ = v___y_3708_;
v___y_3629_ = v___y_3709_;
v___y_3630_ = v___y_3710_;
v___y_3631_ = v___y_3711_;
v___y_3632_ = v___y_3712_;
goto v___jp_3610_;
}
else
{
lean_object* v_toCold_3724_; lean_object* v_inheritedTraceOptions_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; 
v_toCold_3724_ = lean_ctor_get(v___y_3711_, 0);
v_inheritedTraceOptions_3725_ = lean_ctor_get(v_toCold_3724_, 4);
v___x_3726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3725_, v_options_3722_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_inc_ref(v_self_3713_);
lean_inc(v_size_3715_);
lean_inc_ref(v_next_3714_);
v___y_3611_ = v_next_3714_;
v___y_3612_ = v_a_3719_;
v___y_3613_ = v_heqProofs_3717_;
v___y_3614_ = v_fns_u2082_3702_;
v___y_3615_ = v___y_3698_;
v___y_3616_ = v_size_3715_;
v___y_3617_ = v_self_3713_;
v___y_3618_ = v_hasLambdas_3716_;
v___y_3619_ = v___y_3699_;
v___y_3620_ = v___y_3700_;
v___y_3621_ = v___y_3701_;
v___y_3622_ = v_root_3720_;
v___y_3623_ = v___y_3703_;
v___y_3624_ = v___y_3704_;
v___y_3625_ = v___y_3705_;
v___y_3626_ = v___y_3706_;
v___y_3627_ = v___y_3707_;
v___y_3628_ = v___y_3708_;
v___y_3629_ = v___y_3709_;
v___y_3630_ = v___y_3710_;
v___y_3631_ = v___y_3711_;
v___y_3632_ = v___y_3712_;
goto v___jp_3610_;
}
else
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_Meta_Grind_updateLastTag(v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v___x_3729_; 
lean_dec_ref_known(v___x_3728_, 1);
lean_inc_ref(v_lhs_3437_);
v___x_3729_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3437_, v___y_3703_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3731_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
lean_inc_ref(v_root_3720_);
v___x_3731_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3720_, v___y_3703_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
v___x_3733_ = lean_st_ref_get(v___y_3703_);
lean_inc_ref(v_lhs_3437_);
v___x_3734_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3733_, v_lhs_3437_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___x_3733_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3736_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___x_3734_, 1);
v___x_3736_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3735_, v___y_3703_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___x_3736_, 1);
v___x_3738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3739_, 0, v_a_3730_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
lean_ctor_set(v___x_3740_, 1, v_a_3732_);
v___x_3741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3740_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
v___x_3743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
lean_ctor_set(v___x_3743_, 1, v_a_3737_);
v___x_3744_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3696_, v___x_3743_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_dec_ref_known(v___x_3744_, 1);
lean_inc_ref(v_self_3713_);
lean_inc(v_size_3715_);
lean_inc_ref(v_next_3714_);
v___y_3611_ = v_next_3714_;
v___y_3612_ = v_a_3719_;
v___y_3613_ = v_heqProofs_3717_;
v___y_3614_ = v_fns_u2082_3702_;
v___y_3615_ = v___y_3698_;
v___y_3616_ = v_size_3715_;
v___y_3617_ = v_self_3713_;
v___y_3618_ = v_hasLambdas_3716_;
v___y_3619_ = v___y_3699_;
v___y_3620_ = v___y_3700_;
v___y_3621_ = v___y_3701_;
v___y_3622_ = v_root_3720_;
v___y_3623_ = v___y_3703_;
v___y_3624_ = v___y_3704_;
v___y_3625_ = v___y_3705_;
v___y_3626_ = v___y_3706_;
v___y_3627_ = v___y_3707_;
v___y_3628_ = v___y_3708_;
v___y_3629_ = v___y_3709_;
v___y_3630_ = v___y_3710_;
v___y_3631_ = v___y_3711_;
v___y_3632_ = v___y_3712_;
goto v___jp_3610_;
}
else
{
lean_dec_ref(v_root_3720_);
lean_dec(v_a_3719_);
lean_dec_ref(v_fns_u2082_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_lhs_3437_);
return v___x_3744_;
}
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec(v_a_3732_);
lean_dec(v_a_3730_);
lean_dec_ref(v_root_3720_);
lean_dec(v_a_3719_);
lean_dec_ref(v_fns_u2082_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_lhs_3437_);
v_a_3745_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3736_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3736_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_dec(v_a_3732_);
lean_dec(v_a_3730_);
lean_dec_ref(v_root_3720_);
lean_dec(v_a_3719_);
lean_dec_ref(v_fns_u2082_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_lhs_3437_);
v_a_3753_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3734_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3734_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3730_);
lean_dec_ref(v_root_3720_);
lean_dec(v_a_3719_);
lean_dec_ref(v_fns_u2082_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_lhs_3437_);
v_a_3761_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3731_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3731_);
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
lean_dec(v_a_3719_);
lean_dec_ref(v_fns_u2082_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_lhs_3437_);
v_a_3769_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3729_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3729_);
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
lean_dec(v_a_3719_);
lean_dec_ref(v_fns_u2082_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_lhs_3437_);
return v___x_3728_;
}
}
}
}
else
{
lean_dec_ref(v_root_3720_);
lean_dec(v_a_3719_);
lean_dec_ref(v_fns_u2082_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_lhs_3437_);
return v___x_3721_;
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec_ref(v_fns_u2082_3702_);
lean_dec_ref(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhs_3437_);
v_a_3777_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3718_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3718_);
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
v___jp_3785_:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3800_ = lean_array_get_size(v___y_3788_);
v___x_3801_ = lean_unsigned_to_nat(0u);
v___x_3802_ = lean_nat_dec_eq(v___x_3800_, v___x_3801_);
if (v___x_3802_ == 0)
{
lean_object* v_self_3803_; lean_object* v___x_3804_; 
v_self_3803_ = lean_ctor_get(v_lhsRoot_3441_, 0);
lean_inc_ref(v_self_3803_);
v___x_3804_ = l_Lean_Meta_Grind_getFnRoots(v_self_3803_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v___y_3698_ = v___y_3786_;
v___y_3699_ = v___y_3787_;
v___y_3700_ = v___y_3788_;
v___y_3701_ = v_fns_u2081_3789_;
v_fns_u2082_3702_ = v_a_3805_;
v___y_3703_ = v___y_3790_;
v___y_3704_ = v___y_3791_;
v___y_3705_ = v___y_3792_;
v___y_3706_ = v___y_3793_;
v___y_3707_ = v___y_3794_;
v___y_3708_ = v___y_3795_;
v___y_3709_ = v___y_3796_;
v___y_3710_ = v___y_3797_;
v___y_3711_ = v___y_3798_;
v___y_3712_ = v___y_3799_;
goto v___jp_3697_;
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref(v_fns_u2081_3789_);
lean_dec_ref(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhs_3437_);
v_a_3806_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3804_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3804_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
else
{
lean_object* v___x_3814_; 
v___x_3814_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3698_ = v___y_3786_;
v___y_3699_ = v___y_3787_;
v___y_3700_ = v___y_3788_;
v___y_3701_ = v_fns_u2081_3789_;
v_fns_u2082_3702_ = v___x_3814_;
v___y_3703_ = v___y_3790_;
v___y_3704_ = v___y_3791_;
v___y_3705_ = v___y_3792_;
v___y_3706_ = v___y_3793_;
v___y_3707_ = v___y_3794_;
v___y_3708_ = v___y_3795_;
v___y_3709_ = v___y_3796_;
v___y_3710_ = v___y_3797_;
v___y_3711_ = v___y_3798_;
v___y_3712_ = v___y_3799_;
goto v___jp_3697_;
}
}
v___jp_3815_:
{
lean_object* v___x_3826_; 
lean_inc_ref(v_lhs_3437_);
v___x_3826_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3437_, v___y_3816_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3894_; 
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3826_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; 
v_unused_3895_ = lean_ctor_get(v___x_3826_, 0);
lean_dec(v_unused_3895_);
v___x_3828_ = v___x_3826_;
v_isShared_3829_ = v_isSharedCheck_3894_;
goto v_resetjp_3827_;
}
else
{
lean_dec(v___x_3826_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3894_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v_self_3830_; lean_object* v_next_3831_; lean_object* v_root_3832_; lean_object* v_congr_3833_; lean_object* v_size_3834_; uint8_t v_interpreted_3835_; uint8_t v_ctor_3836_; uint8_t v_hasLambdas_3837_; uint8_t v_heqProofs_3838_; lean_object* v_idx_3839_; lean_object* v_generation_3840_; lean_object* v_mt_3841_; lean_object* v_sTerms_3842_; uint8_t v_funCC_3843_; lean_object* v_ematchDiagSource_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3891_; 
v_self_3830_ = lean_ctor_get(v_lhsNode_3439_, 0);
v_next_3831_ = lean_ctor_get(v_lhsNode_3439_, 1);
v_root_3832_ = lean_ctor_get(v_lhsNode_3439_, 2);
v_congr_3833_ = lean_ctor_get(v_lhsNode_3439_, 3);
v_size_3834_ = lean_ctor_get(v_lhsNode_3439_, 6);
v_interpreted_3835_ = lean_ctor_get_uint8(v_lhsNode_3439_, sizeof(void*)*12 + 1);
v_ctor_3836_ = lean_ctor_get_uint8(v_lhsNode_3439_, sizeof(void*)*12 + 2);
v_hasLambdas_3837_ = lean_ctor_get_uint8(v_lhsNode_3439_, sizeof(void*)*12 + 3);
v_heqProofs_3838_ = lean_ctor_get_uint8(v_lhsNode_3439_, sizeof(void*)*12 + 4);
v_idx_3839_ = lean_ctor_get(v_lhsNode_3439_, 7);
v_generation_3840_ = lean_ctor_get(v_lhsNode_3439_, 8);
v_mt_3841_ = lean_ctor_get(v_lhsNode_3439_, 9);
v_sTerms_3842_ = lean_ctor_get(v_lhsNode_3439_, 10);
v_funCC_3843_ = lean_ctor_get_uint8(v_lhsNode_3439_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3844_ = lean_ctor_get(v_lhsNode_3439_, 11);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_lhsNode_3439_);
if (v_isSharedCheck_3891_ == 0)
{
lean_object* v_unused_3892_; lean_object* v_unused_3893_; 
v_unused_3892_ = lean_ctor_get(v_lhsNode_3439_, 5);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_lhsNode_3439_, 4);
lean_dec(v_unused_3893_);
v___x_3846_ = v_lhsNode_3439_;
v_isShared_3847_ = v_isSharedCheck_3891_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_ematchDiagSource_3844_);
lean_inc(v_sTerms_3842_);
lean_inc(v_mt_3841_);
lean_inc(v_generation_3840_);
lean_inc(v_idx_3839_);
lean_inc(v_size_3834_);
lean_inc(v_congr_3833_);
lean_inc(v_root_3832_);
lean_inc(v_next_3831_);
lean_inc(v_self_3830_);
lean_dec(v_lhsNode_3439_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3891_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3829_ == 0)
{
lean_ctor_set_tag(v___x_3828_, 1);
lean_ctor_set(v___x_3828_, 0, v_rhs_3438_);
v___x_3849_ = v___x_3828_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_rhs_3438_);
v___x_3849_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
lean_object* v___x_3850_; lean_object* v___x_3852_; 
v___x_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3850_, 0, v_proof_3435_);
lean_inc_ref(v_root_3832_);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 5, v___x_3850_);
lean_ctor_set(v___x_3846_, 4, v___x_3849_);
v___x_3852_ = v___x_3846_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_self_3830_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v_next_3831_);
lean_ctor_set(v_reuseFailAlloc_3889_, 2, v_root_3832_);
lean_ctor_set(v_reuseFailAlloc_3889_, 3, v_congr_3833_);
lean_ctor_set(v_reuseFailAlloc_3889_, 4, v___x_3849_);
lean_ctor_set(v_reuseFailAlloc_3889_, 5, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3889_, 6, v_size_3834_);
lean_ctor_set(v_reuseFailAlloc_3889_, 7, v_idx_3839_);
lean_ctor_set(v_reuseFailAlloc_3889_, 8, v_generation_3840_);
lean_ctor_set(v_reuseFailAlloc_3889_, 9, v_mt_3841_);
lean_ctor_set(v_reuseFailAlloc_3889_, 10, v_sTerms_3842_);
lean_ctor_set(v_reuseFailAlloc_3889_, 11, v_ematchDiagSource_3844_);
lean_ctor_set_uint8(v_reuseFailAlloc_3889_, sizeof(void*)*12 + 1, v_interpreted_3835_);
lean_ctor_set_uint8(v_reuseFailAlloc_3889_, sizeof(void*)*12 + 2, v_ctor_3836_);
lean_ctor_set_uint8(v_reuseFailAlloc_3889_, sizeof(void*)*12 + 3, v_hasLambdas_3837_);
lean_ctor_set_uint8(v_reuseFailAlloc_3889_, sizeof(void*)*12 + 4, v_heqProofs_3838_);
lean_ctor_set_uint8(v_reuseFailAlloc_3889_, sizeof(void*)*12 + 5, v_funCC_3843_);
v___x_3852_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3853_; 
lean_ctor_set_uint8(v___x_3852_, sizeof(void*)*12, v_flipped_3443_);
lean_inc_ref(v_lhs_3437_);
v___x_3853_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3437_, v___x_3852_, v___y_3816_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v___x_3854_; 
lean_dec_ref_known(v___x_3853_, 1);
v___x_3854_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3441_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3856_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v___x_3856_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3442_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
v___x_3858_ = lean_array_get_size(v_a_3855_);
v___x_3859_ = lean_unsigned_to_nat(0u);
v___x_3860_ = lean_nat_dec_eq(v___x_3858_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v_self_3861_; lean_object* v___x_3862_; 
v_self_3861_ = lean_ctor_get(v_rhsRoot_3442_, 0);
lean_inc_ref(v_self_3861_);
v___x_3862_ = l_Lean_Meta_Grind_getFnRoots(v_self_3861_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___x_3862_, 1);
v___y_3786_ = v_root_3832_;
v___y_3787_ = v_a_3855_;
v___y_3788_ = v_a_3857_;
v_fns_u2081_3789_ = v_a_3863_;
v___y_3790_ = v___y_3816_;
v___y_3791_ = v___y_3817_;
v___y_3792_ = v___y_3818_;
v___y_3793_ = v___y_3819_;
v___y_3794_ = v___y_3820_;
v___y_3795_ = v___y_3821_;
v___y_3796_ = v___y_3822_;
v___y_3797_ = v___y_3823_;
v___y_3798_ = v___y_3824_;
v___y_3799_ = v___y_3825_;
goto v___jp_3785_;
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec(v_a_3857_);
lean_dec(v_a_3855_);
lean_dec_ref(v_root_3832_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhs_3437_);
v_a_3864_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3862_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3862_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
else
{
lean_object* v___x_3872_; 
v___x_3872_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3786_ = v_root_3832_;
v___y_3787_ = v_a_3855_;
v___y_3788_ = v_a_3857_;
v_fns_u2081_3789_ = v___x_3872_;
v___y_3790_ = v___y_3816_;
v___y_3791_ = v___y_3817_;
v___y_3792_ = v___y_3818_;
v___y_3793_ = v___y_3819_;
v___y_3794_ = v___y_3820_;
v___y_3795_ = v___y_3821_;
v___y_3796_ = v___y_3822_;
v___y_3797_ = v___y_3823_;
v___y_3798_ = v___y_3824_;
v___y_3799_ = v___y_3825_;
goto v___jp_3785_;
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec(v_a_3855_);
lean_dec_ref(v_root_3832_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhs_3437_);
v_a_3873_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3856_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3856_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec_ref(v_root_3832_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhs_3437_);
v_a_3881_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3854_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3854_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
else
{
lean_dec_ref(v_root_3832_);
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhs_3437_);
return v___x_3853_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3442_);
lean_dec_ref(v_lhsRoot_3441_);
lean_dec_ref(v_rhsNode_3440_);
lean_dec_ref(v_lhsNode_3439_);
lean_dec_ref(v_rhs_3438_);
lean_dec_ref(v_lhs_3437_);
lean_dec_ref(v_proof_3435_);
return v___x_3826_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3926_ = _args[0];
lean_object* v_isHEq_3927_ = _args[1];
lean_object* v_lhs_3928_ = _args[2];
lean_object* v_rhs_3929_ = _args[3];
lean_object* v_lhsNode_3930_ = _args[4];
lean_object* v_rhsNode_3931_ = _args[5];
lean_object* v_lhsRoot_3932_ = _args[6];
lean_object* v_rhsRoot_3933_ = _args[7];
lean_object* v_flipped_3934_ = _args[8];
lean_object* v_a_3935_ = _args[9];
lean_object* v_a_3936_ = _args[10];
lean_object* v_a_3937_ = _args[11];
lean_object* v_a_3938_ = _args[12];
lean_object* v_a_3939_ = _args[13];
lean_object* v_a_3940_ = _args[14];
lean_object* v_a_3941_ = _args[15];
lean_object* v_a_3942_ = _args[16];
lean_object* v_a_3943_ = _args[17];
lean_object* v_a_3944_ = _args[18];
lean_object* v_a_3945_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3946_; uint8_t v_flipped_boxed_3947_; lean_object* v_res_3948_; 
v_isHEq_boxed_3946_ = lean_unbox(v_isHEq_3927_);
v_flipped_boxed_3947_ = lean_unbox(v_flipped_3934_);
v_res_3948_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3926_, v_isHEq_boxed_3946_, v_lhs_3928_, v_rhs_3929_, v_lhsNode_3930_, v_rhsNode_3931_, v_lhsRoot_3932_, v_rhsRoot_3933_, v_flipped_boxed_3947_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
lean_dec(v_a_3935_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3949_, lean_object* v_as_x27_3950_, lean_object* v_b_3951_, lean_object* v_a_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3950_, v_b_3951_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3965_, lean_object* v_as_x27_3966_, lean_object* v_b_3967_, lean_object* v_a_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3965_, v_as_x27_3966_, v_b_3967_, v_a_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec(v_as_x27_3966_);
lean_dec(v_as_3965_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3981_, lean_object* v_as_x27_3982_, lean_object* v_b_3983_, lean_object* v_a_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3982_, v_b_3983_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3997_, lean_object* v_as_x27_3998_, lean_object* v_b_3999_, lean_object* v_a_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3997_, v_as_x27_3998_, v_b_3999_, v_a_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec(v_as_x27_3998_);
lean_dec(v_as_3997_);
return v_res_4012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4015_ = l_Lean_stringToMessageData(v___x_4014_);
return v___x_4015_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4021_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4022_ = l_Lean_Name_append(v___x_4021_, v___x_4020_);
return v___x_4022_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4025_ = l_Lean_stringToMessageData(v___x_4024_);
return v___x_4025_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4028_ = l_Lean_stringToMessageData(v___x_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4029_, lean_object* v_rhs_4030_, lean_object* v_proof_4031_, uint8_t v_isHEq_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = lean_st_ref_get(v_a_4033_);
lean_inc_ref(v_lhs_4029_);
v___x_4048_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4047_, v_lhs_4029_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
lean_dec(v___x_4047_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref_known(v___x_4048_, 1);
v___x_4050_ = lean_st_ref_get(v_a_4033_);
lean_inc_ref(v_rhs_4030_);
v___x_4051_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4050_, v_rhs_4030_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
lean_dec(v___x_4050_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v_root_4053_; lean_object* v_root_4054_; size_t v___x_4055_; size_t v___x_4056_; uint8_t v___x_4057_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc(v_a_4052_);
lean_dec_ref_known(v___x_4051_, 1);
v_root_4053_ = lean_ctor_get(v_a_4049_, 2);
v_root_4054_ = lean_ctor_get(v_a_4052_, 2);
v___x_4055_ = lean_ptr_addr(v_root_4053_);
v___x_4056_ = lean_ptr_addr(v_root_4054_);
v___x_4057_ = lean_usize_dec_eq(v___x_4055_, v___x_4056_);
if (v___x_4057_ == 0)
{
lean_object* v_options_4058_; lean_object* v_toCold_4059_; uint8_t v_hasTrace_4060_; uint8_t v___x_4061_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4099_; lean_object* v___y_4100_; uint8_t v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4127_; lean_object* v___y_4128_; uint8_t v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4157_; lean_object* v___y_4158_; uint8_t v___y_4159_; uint8_t v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; uint8_t v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; uint8_t v___y_4186_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; uint8_t v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; uint8_t v___y_4202_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v_size_4208_; uint8_t v_interpreted_4209_; uint8_t v_ctor_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; uint8_t v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; uint8_t v___y_4221_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; uint8_t v_ctor_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; uint8_t v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; uint8_t v___y_4239_; lean_object* v___y_4247_; lean_object* v___y_4248_; uint8_t v_valueInconsistency_4249_; uint8_t v_trueEqFalse_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4280_; lean_object* v___y_4281_; uint8_t v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4316_; 
v_options_4058_ = lean_ctor_get(v_a_4041_, 1);
v_toCold_4059_ = lean_ctor_get(v_a_4041_, 0);
v_hasTrace_4060_ = lean_ctor_get_uint8(v_options_4058_, sizeof(void*)*1);
v___x_4061_ = 1;
if (v_hasTrace_4060_ == 0)
{
v___y_4307_ = v_a_4033_;
v___y_4308_ = v_a_4034_;
v___y_4309_ = v_a_4035_;
v___y_4310_ = v_a_4036_;
v___y_4311_ = v_a_4037_;
v___y_4312_ = v_a_4038_;
v___y_4313_ = v_a_4039_;
v___y_4314_ = v_a_4040_;
v___y_4315_ = v_a_4041_;
v___y_4316_ = v_a_4042_;
goto v___jp_4306_;
}
else
{
lean_object* v_inheritedTraceOptions_4350_; lean_object* v___x_4351_; lean_object* v_____do__lift_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___x_4366_; uint8_t v___x_4367_; 
v_inheritedTraceOptions_4350_ = lean_ctor_get(v_toCold_4059_, 4);
v___x_4351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4366_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4367_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4350_, v_options_4058_, v___x_4366_);
if (v___x_4367_ == 0)
{
v___y_4307_ = v_a_4033_;
v___y_4308_ = v_a_4034_;
v___y_4309_ = v_a_4035_;
v___y_4310_ = v_a_4036_;
v___y_4311_ = v_a_4037_;
v___y_4312_ = v_a_4038_;
v___y_4313_ = v_a_4039_;
v___y_4314_ = v_a_4040_;
v___y_4315_ = v_a_4041_;
v___y_4316_ = v_a_4042_;
goto v___jp_4306_;
}
else
{
lean_object* v___x_4368_; 
v___x_4368_ = l_Lean_Meta_Grind_updateLastTag(v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_dec_ref_known(v___x_4368_, 1);
if (v_isHEq_4032_ == 0)
{
lean_object* v___x_4369_; 
lean_inc_ref(v_rhs_4030_);
lean_inc_ref(v_lhs_4029_);
v___x_4369_ = l_Lean_Meta_mkEq(v_lhs_4029_, v_rhs_4030_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4370_);
lean_dec_ref_known(v___x_4369_, 1);
v_____do__lift_4353_ = v_a_4370_;
v___y_4354_ = v_a_4033_;
v___y_4355_ = v_a_4034_;
v___y_4356_ = v_a_4035_;
v___y_4357_ = v_a_4036_;
v___y_4358_ = v_a_4037_;
v___y_4359_ = v_a_4038_;
v___y_4360_ = v_a_4039_;
v___y_4361_ = v_a_4040_;
v___y_4362_ = v_a_4041_;
v___y_4363_ = v_a_4042_;
goto v___jp_4352_;
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec(v_a_4052_);
lean_dec(v_a_4049_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
v_a_4371_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4369_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4369_);
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
lean_object* v___x_4379_; 
lean_inc_ref(v_rhs_4030_);
lean_inc_ref(v_lhs_4029_);
v___x_4379_ = l_Lean_Meta_mkHEq(v_lhs_4029_, v_rhs_4030_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4379_, 1);
v_____do__lift_4353_ = v_a_4380_;
v___y_4354_ = v_a_4033_;
v___y_4355_ = v_a_4034_;
v___y_4356_ = v_a_4035_;
v___y_4357_ = v_a_4036_;
v___y_4358_ = v_a_4037_;
v___y_4359_ = v_a_4038_;
v___y_4360_ = v_a_4039_;
v___y_4361_ = v_a_4040_;
v___y_4362_ = v_a_4041_;
v___y_4363_ = v_a_4042_;
goto v___jp_4352_;
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec(v_a_4052_);
lean_dec(v_a_4049_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
v_a_4381_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4379_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4379_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
else
{
lean_dec(v_a_4052_);
lean_dec(v_a_4049_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
return v___x_4368_;
}
}
v___jp_4352_:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4364_ = l_Lean_MessageData_ofExpr(v_____do__lift_4353_);
v___x_4365_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4351_, v___x_4364_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_dec_ref_known(v___x_4365_, 1);
v___y_4307_ = v___y_4354_;
v___y_4308_ = v___y_4355_;
v___y_4309_ = v___y_4356_;
v___y_4310_ = v___y_4357_;
v___y_4311_ = v___y_4358_;
v___y_4312_ = v___y_4359_;
v___y_4313_ = v___y_4360_;
v___y_4314_ = v___y_4361_;
v___y_4315_ = v___y_4362_;
v___y_4316_ = v___y_4363_;
goto v___jp_4306_;
}
else
{
lean_dec(v_a_4052_);
lean_dec(v_a_4049_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
return v___x_4365_;
}
}
}
v___jp_4062_:
{
lean_object* v_options_4073_; uint8_t v_hasTrace_4074_; 
v_options_4073_ = lean_ctor_get(v___y_4071_, 1);
v_hasTrace_4074_ = lean_ctor_get_uint8(v_options_4073_, sizeof(void*)*1);
if (v_hasTrace_4074_ == 0)
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_Meta_Grind_checkInvariants(v___x_4057_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
return v___x_4075_;
}
else
{
lean_object* v_toCold_4076_; lean_object* v_inheritedTraceOptions_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; 
v_toCold_4076_ = lean_ctor_get(v___y_4071_, 0);
v_inheritedTraceOptions_4077_ = lean_ctor_get(v_toCold_4076_, 4);
v___x_4078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4080_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4077_, v_options_4073_, v___x_4079_);
if (v___x_4080_ == 0)
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Lean_Meta_Grind_checkInvariants(v___x_4057_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
return v___x_4081_;
}
else
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Lean_Meta_Grind_updateLastTag(v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_dec_ref_known(v___x_4082_, 1);
v___x_4083_ = lean_st_ref_get(v___y_4063_);
v___x_4084_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4083_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___x_4083_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___x_4084_, 1);
v___x_4086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
lean_ctor_set(v___x_4087_, 1, v_a_4085_);
v___x_4088_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4078_, v___x_4087_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v___x_4089_; 
lean_dec_ref_known(v___x_4088_, 1);
v___x_4089_ = l_Lean_Meta_Grind_checkInvariants(v___x_4057_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
return v___x_4089_;
}
else
{
return v___x_4088_;
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
v_a_4090_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4084_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4084_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
else
{
return v___x_4082_;
}
}
}
}
v___jp_4098_:
{
lean_object* v___x_4112_; 
v___x_4112_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4102_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; uint8_t v___x_4114_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___x_4112_, 1);
v___x_4114_ = lean_unbox(v_a_4113_);
lean_dec(v_a_4113_);
if (v___x_4114_ == 0)
{
if (v___y_4101_ == 0)
{
lean_dec_ref(v___y_4100_);
lean_dec_ref(v___y_4099_);
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4103_;
v___y_4065_ = v___y_4104_;
v___y_4066_ = v___y_4105_;
v___y_4067_ = v___y_4106_;
v___y_4068_ = v___y_4107_;
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4109_;
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
goto v___jp_4062_;
}
else
{
lean_object* v_self_4115_; lean_object* v_self_4116_; lean_object* v___x_4117_; 
v_self_4115_ = lean_ctor_get(v___y_4100_, 0);
lean_inc_ref(v_self_4115_);
lean_dec_ref(v___y_4100_);
v_self_4116_ = lean_ctor_get(v___y_4099_, 0);
lean_inc_ref(v_self_4116_);
lean_dec_ref(v___y_4099_);
v___x_4117_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4115_, v_self_4116_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_dec_ref_known(v___x_4117_, 1);
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4103_;
v___y_4065_ = v___y_4104_;
v___y_4066_ = v___y_4105_;
v___y_4067_ = v___y_4106_;
v___y_4068_ = v___y_4107_;
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4109_;
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
goto v___jp_4062_;
}
else
{
return v___x_4117_;
}
}
}
else
{
lean_dec_ref(v___y_4100_);
lean_dec_ref(v___y_4099_);
v___y_4063_ = v___y_4102_;
v___y_4064_ = v___y_4103_;
v___y_4065_ = v___y_4104_;
v___y_4066_ = v___y_4105_;
v___y_4067_ = v___y_4106_;
v___y_4068_ = v___y_4107_;
v___y_4069_ = v___y_4108_;
v___y_4070_ = v___y_4109_;
v___y_4071_ = v___y_4110_;
v___y_4072_ = v___y_4111_;
goto v___jp_4062_;
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec_ref(v___y_4100_);
lean_dec_ref(v___y_4099_);
v_a_4118_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4112_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4112_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
v___jp_4126_:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4130_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; uint8_t v___x_4142_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v___x_4142_ = lean_unbox(v_a_4141_);
lean_dec(v_a_4141_);
if (v___x_4142_ == 0)
{
uint8_t v_ctor_4143_; 
v_ctor_4143_ = lean_ctor_get_uint8(v___y_4128_, sizeof(void*)*12 + 2);
if (v_ctor_4143_ == 0)
{
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4130_;
v___y_4103_ = v___y_4131_;
v___y_4104_ = v___y_4132_;
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
v___y_4108_ = v___y_4136_;
v___y_4109_ = v___y_4137_;
v___y_4110_ = v___y_4138_;
v___y_4111_ = v___y_4139_;
goto v___jp_4098_;
}
else
{
uint8_t v_ctor_4144_; 
v_ctor_4144_ = lean_ctor_get_uint8(v___y_4127_, sizeof(void*)*12 + 2);
if (v_ctor_4144_ == 0)
{
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4130_;
v___y_4103_ = v___y_4131_;
v___y_4104_ = v___y_4132_;
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
v___y_4108_ = v___y_4136_;
v___y_4109_ = v___y_4137_;
v___y_4110_ = v___y_4138_;
v___y_4111_ = v___y_4139_;
goto v___jp_4098_;
}
else
{
lean_object* v_self_4145_; lean_object* v_self_4146_; lean_object* v___x_4147_; 
v_self_4145_ = lean_ctor_get(v___y_4128_, 0);
v_self_4146_ = lean_ctor_get(v___y_4127_, 0);
lean_inc_ref(v_self_4146_);
lean_inc_ref(v_self_4145_);
v___x_4147_ = l_Lean_Meta_Grind_propagateCtor(v_self_4145_, v_self_4146_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_dec_ref_known(v___x_4147_, 1);
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4130_;
v___y_4103_ = v___y_4131_;
v___y_4104_ = v___y_4132_;
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
v___y_4108_ = v___y_4136_;
v___y_4109_ = v___y_4137_;
v___y_4110_ = v___y_4138_;
v___y_4111_ = v___y_4139_;
goto v___jp_4098_;
}
else
{
lean_dec_ref(v___y_4128_);
lean_dec_ref(v___y_4127_);
return v___x_4147_;
}
}
}
}
else
{
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4130_;
v___y_4103_ = v___y_4131_;
v___y_4104_ = v___y_4132_;
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
v___y_4108_ = v___y_4136_;
v___y_4109_ = v___y_4137_;
v___y_4110_ = v___y_4138_;
v___y_4111_ = v___y_4139_;
goto v___jp_4098_;
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec_ref(v___y_4128_);
lean_dec_ref(v___y_4127_);
v_a_4148_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4140_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4140_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
v___jp_4156_:
{
if (v___y_4160_ == 0)
{
v___y_4127_ = v___y_4157_;
v___y_4128_ = v___y_4158_;
v___y_4129_ = v___y_4159_;
v___y_4130_ = v___y_4161_;
v___y_4131_ = v___y_4162_;
v___y_4132_ = v___y_4163_;
v___y_4133_ = v___y_4164_;
v___y_4134_ = v___y_4165_;
v___y_4135_ = v___y_4166_;
v___y_4136_ = v___y_4167_;
v___y_4137_ = v___y_4168_;
v___y_4138_ = v___y_4169_;
v___y_4139_ = v___y_4170_;
goto v___jp_4126_;
}
else
{
lean_object* v___x_4171_; 
v___x_4171_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_dec_ref_known(v___x_4171_, 1);
v___y_4127_ = v___y_4157_;
v___y_4128_ = v___y_4158_;
v___y_4129_ = v___y_4159_;
v___y_4130_ = v___y_4161_;
v___y_4131_ = v___y_4162_;
v___y_4132_ = v___y_4163_;
v___y_4133_ = v___y_4164_;
v___y_4134_ = v___y_4165_;
v___y_4135_ = v___y_4166_;
v___y_4136_ = v___y_4167_;
v___y_4137_ = v___y_4168_;
v___y_4138_ = v___y_4169_;
v___y_4139_ = v___y_4170_;
goto v___jp_4126_;
}
else
{
lean_dec_ref(v___y_4158_);
lean_dec_ref(v___y_4157_);
return v___x_4171_;
}
}
}
v___jp_4172_:
{
lean_object* v___x_4187_; 
lean_inc_ref(v___y_4177_);
lean_inc_ref(v___y_4175_);
v___x_4187_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4031_, v_isHEq_4032_, v_rhs_4030_, v_lhs_4029_, v_a_4052_, v_a_4049_, v___y_4175_, v___y_4177_, v___x_4061_, v___y_4178_, v___y_4179_, v___y_4184_, v___y_4174_, v___y_4176_, v___y_4181_, v___y_4173_, v___y_4185_, v___y_4182_, v___y_4183_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_dec_ref_known(v___x_4187_, 1);
v___y_4157_ = v___y_4175_;
v___y_4158_ = v___y_4177_;
v___y_4159_ = v___y_4180_;
v___y_4160_ = v___y_4186_;
v___y_4161_ = v___y_4178_;
v___y_4162_ = v___y_4179_;
v___y_4163_ = v___y_4184_;
v___y_4164_ = v___y_4174_;
v___y_4165_ = v___y_4176_;
v___y_4166_ = v___y_4181_;
v___y_4167_ = v___y_4173_;
v___y_4168_ = v___y_4185_;
v___y_4169_ = v___y_4182_;
v___y_4170_ = v___y_4183_;
goto v___jp_4156_;
}
else
{
lean_dec_ref(v___y_4177_);
lean_dec_ref(v___y_4175_);
return v___x_4187_;
}
}
v___jp_4188_:
{
lean_object* v___x_4203_; 
lean_inc_ref(v___y_4191_);
lean_inc_ref(v___y_4193_);
v___x_4203_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4031_, v_isHEq_4032_, v_lhs_4029_, v_rhs_4030_, v_a_4049_, v_a_4052_, v___y_4193_, v___y_4191_, v___x_4057_, v___y_4194_, v___y_4195_, v___y_4200_, v___y_4190_, v___y_4192_, v___y_4197_, v___y_4189_, v___y_4201_, v___y_4198_, v___y_4199_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_dec_ref_known(v___x_4203_, 1);
v___y_4157_ = v___y_4191_;
v___y_4158_ = v___y_4193_;
v___y_4159_ = v___y_4196_;
v___y_4160_ = v___y_4202_;
v___y_4161_ = v___y_4194_;
v___y_4162_ = v___y_4195_;
v___y_4163_ = v___y_4200_;
v___y_4164_ = v___y_4190_;
v___y_4165_ = v___y_4192_;
v___y_4166_ = v___y_4197_;
v___y_4167_ = v___y_4189_;
v___y_4168_ = v___y_4201_;
v___y_4169_ = v___y_4198_;
v___y_4170_ = v___y_4199_;
goto v___jp_4156_;
}
else
{
lean_dec_ref(v___y_4193_);
lean_dec_ref(v___y_4191_);
return v___x_4203_;
}
}
v___jp_4204_:
{
lean_object* v_size_4222_; uint8_t v___x_4223_; 
v_size_4222_ = lean_ctor_get(v___y_4212_, 6);
v___x_4223_ = lean_nat_dec_lt(v_size_4208_, v_size_4222_);
lean_dec(v_size_4208_);
if (v___x_4223_ == 0)
{
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4206_;
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4211_;
v___y_4193_ = v___y_4212_;
v___y_4194_ = v___y_4213_;
v___y_4195_ = v___y_4214_;
v___y_4196_ = v___y_4215_;
v___y_4197_ = v___y_4216_;
v___y_4198_ = v___y_4217_;
v___y_4199_ = v___y_4218_;
v___y_4200_ = v___y_4219_;
v___y_4201_ = v___y_4220_;
v___y_4202_ = v___y_4221_;
goto v___jp_4188_;
}
else
{
if (v_interpreted_4209_ == 0)
{
if (v_ctor_4210_ == 0)
{
v___y_4173_ = v___y_4205_;
v___y_4174_ = v___y_4206_;
v___y_4175_ = v___y_4207_;
v___y_4176_ = v___y_4211_;
v___y_4177_ = v___y_4212_;
v___y_4178_ = v___y_4213_;
v___y_4179_ = v___y_4214_;
v___y_4180_ = v___y_4215_;
v___y_4181_ = v___y_4216_;
v___y_4182_ = v___y_4217_;
v___y_4183_ = v___y_4218_;
v___y_4184_ = v___y_4219_;
v___y_4185_ = v___y_4220_;
v___y_4186_ = v___y_4221_;
goto v___jp_4172_;
}
else
{
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4206_;
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4211_;
v___y_4193_ = v___y_4212_;
v___y_4194_ = v___y_4213_;
v___y_4195_ = v___y_4214_;
v___y_4196_ = v___y_4215_;
v___y_4197_ = v___y_4216_;
v___y_4198_ = v___y_4217_;
v___y_4199_ = v___y_4218_;
v___y_4200_ = v___y_4219_;
v___y_4201_ = v___y_4220_;
v___y_4202_ = v___y_4221_;
goto v___jp_4188_;
}
}
else
{
v___y_4189_ = v___y_4205_;
v___y_4190_ = v___y_4206_;
v___y_4191_ = v___y_4207_;
v___y_4192_ = v___y_4211_;
v___y_4193_ = v___y_4212_;
v___y_4194_ = v___y_4213_;
v___y_4195_ = v___y_4214_;
v___y_4196_ = v___y_4215_;
v___y_4197_ = v___y_4216_;
v___y_4198_ = v___y_4217_;
v___y_4199_ = v___y_4218_;
v___y_4200_ = v___y_4219_;
v___y_4201_ = v___y_4220_;
v___y_4202_ = v___y_4221_;
goto v___jp_4188_;
}
}
}
v___jp_4224_:
{
if (v_ctor_4230_ == 0)
{
lean_object* v_size_4240_; uint8_t v_interpreted_4241_; uint8_t v_ctor_4242_; 
v_size_4240_ = lean_ctor_get(v___y_4227_, 6);
lean_inc(v_size_4240_);
v_interpreted_4241_ = lean_ctor_get_uint8(v___y_4227_, sizeof(void*)*12 + 1);
v_ctor_4242_ = lean_ctor_get_uint8(v___y_4227_, sizeof(void*)*12 + 2);
v___y_4205_ = v___y_4225_;
v___y_4206_ = v___y_4226_;
v___y_4207_ = v___y_4227_;
v_size_4208_ = v_size_4240_;
v_interpreted_4209_ = v_interpreted_4241_;
v_ctor_4210_ = v_ctor_4242_;
v___y_4211_ = v___y_4228_;
v___y_4212_ = v___y_4229_;
v___y_4213_ = v___y_4231_;
v___y_4214_ = v___y_4232_;
v___y_4215_ = v___y_4233_;
v___y_4216_ = v___y_4234_;
v___y_4217_ = v___y_4235_;
v___y_4218_ = v___y_4236_;
v___y_4219_ = v___y_4237_;
v___y_4220_ = v___y_4238_;
v___y_4221_ = v___y_4239_;
goto v___jp_4204_;
}
else
{
uint8_t v_ctor_4243_; 
v_ctor_4243_ = lean_ctor_get_uint8(v___y_4227_, sizeof(void*)*12 + 2);
if (v_ctor_4243_ == 0)
{
v___y_4173_ = v___y_4225_;
v___y_4174_ = v___y_4226_;
v___y_4175_ = v___y_4227_;
v___y_4176_ = v___y_4228_;
v___y_4177_ = v___y_4229_;
v___y_4178_ = v___y_4231_;
v___y_4179_ = v___y_4232_;
v___y_4180_ = v___y_4233_;
v___y_4181_ = v___y_4234_;
v___y_4182_ = v___y_4235_;
v___y_4183_ = v___y_4236_;
v___y_4184_ = v___y_4237_;
v___y_4185_ = v___y_4238_;
v___y_4186_ = v___y_4239_;
goto v___jp_4172_;
}
else
{
lean_object* v_size_4244_; uint8_t v_interpreted_4245_; 
v_size_4244_ = lean_ctor_get(v___y_4227_, 6);
lean_inc(v_size_4244_);
v_interpreted_4245_ = lean_ctor_get_uint8(v___y_4227_, sizeof(void*)*12 + 1);
v___y_4205_ = v___y_4225_;
v___y_4206_ = v___y_4226_;
v___y_4207_ = v___y_4227_;
v_size_4208_ = v_size_4244_;
v_interpreted_4209_ = v_interpreted_4245_;
v_ctor_4210_ = v_ctor_4243_;
v___y_4211_ = v___y_4228_;
v___y_4212_ = v___y_4229_;
v___y_4213_ = v___y_4231_;
v___y_4214_ = v___y_4232_;
v___y_4215_ = v___y_4233_;
v___y_4216_ = v___y_4234_;
v___y_4217_ = v___y_4235_;
v___y_4218_ = v___y_4236_;
v___y_4219_ = v___y_4237_;
v___y_4220_ = v___y_4238_;
v___y_4221_ = v___y_4239_;
goto v___jp_4204_;
}
}
}
v___jp_4246_:
{
uint8_t v_interpreted_4261_; 
v_interpreted_4261_ = lean_ctor_get_uint8(v___y_4248_, sizeof(void*)*12 + 1);
if (v_interpreted_4261_ == 0)
{
uint8_t v_ctor_4262_; 
v_ctor_4262_ = lean_ctor_get_uint8(v___y_4248_, sizeof(void*)*12 + 2);
v___y_4225_ = v___y_4257_;
v___y_4226_ = v___y_4254_;
v___y_4227_ = v___y_4247_;
v___y_4228_ = v___y_4255_;
v___y_4229_ = v___y_4248_;
v_ctor_4230_ = v_ctor_4262_;
v___y_4231_ = v___y_4251_;
v___y_4232_ = v___y_4252_;
v___y_4233_ = v_valueInconsistency_4249_;
v___y_4234_ = v___y_4256_;
v___y_4235_ = v___y_4259_;
v___y_4236_ = v___y_4260_;
v___y_4237_ = v___y_4253_;
v___y_4238_ = v___y_4258_;
v___y_4239_ = v_trueEqFalse_4250_;
goto v___jp_4224_;
}
else
{
uint8_t v_interpreted_4263_; 
v_interpreted_4263_ = lean_ctor_get_uint8(v___y_4247_, sizeof(void*)*12 + 1);
if (v_interpreted_4263_ == 0)
{
v___y_4173_ = v___y_4257_;
v___y_4174_ = v___y_4254_;
v___y_4175_ = v___y_4247_;
v___y_4176_ = v___y_4255_;
v___y_4177_ = v___y_4248_;
v___y_4178_ = v___y_4251_;
v___y_4179_ = v___y_4252_;
v___y_4180_ = v_valueInconsistency_4249_;
v___y_4181_ = v___y_4256_;
v___y_4182_ = v___y_4259_;
v___y_4183_ = v___y_4260_;
v___y_4184_ = v___y_4253_;
v___y_4185_ = v___y_4258_;
v___y_4186_ = v_trueEqFalse_4250_;
goto v___jp_4172_;
}
else
{
uint8_t v_ctor_4264_; 
v_ctor_4264_ = lean_ctor_get_uint8(v___y_4248_, sizeof(void*)*12 + 2);
v___y_4225_ = v___y_4257_;
v___y_4226_ = v___y_4254_;
v___y_4227_ = v___y_4247_;
v___y_4228_ = v___y_4255_;
v___y_4229_ = v___y_4248_;
v_ctor_4230_ = v_ctor_4264_;
v___y_4231_ = v___y_4251_;
v___y_4232_ = v___y_4252_;
v___y_4233_ = v_valueInconsistency_4249_;
v___y_4234_ = v___y_4256_;
v___y_4235_ = v___y_4259_;
v___y_4236_ = v___y_4260_;
v___y_4237_ = v___y_4253_;
v___y_4238_ = v___y_4258_;
v___y_4239_ = v_trueEqFalse_4250_;
goto v___jp_4224_;
}
}
}
v___jp_4265_:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4266_, v___y_4274_, v___y_4268_, v___y_4269_, v___y_4276_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_dec_ref_known(v___x_4278_, 1);
v___y_4247_ = v___y_4267_;
v___y_4248_ = v___y_4273_;
v_valueInconsistency_4249_ = v___x_4057_;
v_trueEqFalse_4250_ = v___x_4061_;
v___y_4251_ = v___y_4266_;
v___y_4252_ = v___y_4272_;
v___y_4253_ = v___y_4271_;
v___y_4254_ = v___y_4275_;
v___y_4255_ = v___y_4270_;
v___y_4256_ = v___y_4277_;
v___y_4257_ = v___y_4274_;
v___y_4258_ = v___y_4268_;
v___y_4259_ = v___y_4269_;
v___y_4260_ = v___y_4276_;
goto v___jp_4246_;
}
else
{
lean_dec_ref(v___y_4273_);
lean_dec_ref(v___y_4267_);
lean_dec(v_a_4052_);
lean_dec(v_a_4049_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
return v___x_4278_;
}
}
v___jp_4279_:
{
if (v___y_4282_ == 0)
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_Meta_Grind_hasSameType(v___y_4288_, v___y_4283_, v___y_4291_, v___y_4284_, v___y_4285_, v___y_4293_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; uint8_t v___x_4297_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
v___x_4297_ = lean_unbox(v_a_4296_);
lean_dec(v_a_4296_);
if (v___x_4297_ == 0)
{
v___y_4247_ = v___y_4280_;
v___y_4248_ = v___y_4290_;
v_valueInconsistency_4249_ = v___x_4057_;
v_trueEqFalse_4250_ = v___x_4057_;
v___y_4251_ = v___y_4281_;
v___y_4252_ = v___y_4289_;
v___y_4253_ = v___y_4287_;
v___y_4254_ = v___y_4292_;
v___y_4255_ = v___y_4286_;
v___y_4256_ = v___y_4294_;
v___y_4257_ = v___y_4291_;
v___y_4258_ = v___y_4284_;
v___y_4259_ = v___y_4285_;
v___y_4260_ = v___y_4293_;
goto v___jp_4246_;
}
else
{
v___y_4247_ = v___y_4280_;
v___y_4248_ = v___y_4290_;
v_valueInconsistency_4249_ = v___x_4061_;
v_trueEqFalse_4250_ = v___x_4057_;
v___y_4251_ = v___y_4281_;
v___y_4252_ = v___y_4289_;
v___y_4253_ = v___y_4287_;
v___y_4254_ = v___y_4292_;
v___y_4255_ = v___y_4286_;
v___y_4256_ = v___y_4294_;
v___y_4257_ = v___y_4291_;
v___y_4258_ = v___y_4284_;
v___y_4259_ = v___y_4285_;
v___y_4260_ = v___y_4293_;
goto v___jp_4246_;
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
lean_dec_ref(v___y_4290_);
lean_dec_ref(v___y_4280_);
lean_dec(v_a_4052_);
lean_dec(v_a_4049_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
v_a_4298_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4295_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4295_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
else
{
lean_dec_ref(v___y_4288_);
lean_dec_ref(v___y_4283_);
v___y_4247_ = v___y_4280_;
v___y_4248_ = v___y_4290_;
v_valueInconsistency_4249_ = v___x_4061_;
v_trueEqFalse_4250_ = v___x_4057_;
v___y_4251_ = v___y_4281_;
v___y_4252_ = v___y_4289_;
v___y_4253_ = v___y_4287_;
v___y_4254_ = v___y_4292_;
v___y_4255_ = v___y_4286_;
v___y_4256_ = v___y_4294_;
v___y_4257_ = v___y_4291_;
v___y_4258_ = v___y_4284_;
v___y_4259_ = v___y_4285_;
v___y_4260_ = v___y_4293_;
goto v___jp_4246_;
}
}
v___jp_4306_:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4317_ = lean_st_ref_get(v___y_4307_);
lean_inc_ref(v_root_4053_);
v___x_4318_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4317_, v_root_4053_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___x_4317_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4319_);
lean_dec_ref_known(v___x_4318_, 1);
v___x_4320_ = lean_st_ref_get(v___y_4307_);
lean_inc_ref(v_root_4054_);
v___x_4321_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4320_, v_root_4054_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
lean_dec(v___x_4320_);
if (lean_obj_tag(v___x_4321_) == 0)
{
uint8_t v_interpreted_4322_; 
v_interpreted_4322_ = lean_ctor_get_uint8(v_a_4319_, sizeof(void*)*12 + 1);
if (v_interpreted_4322_ == 0)
{
lean_object* v_a_4323_; uint8_t v_ctor_4324_; 
v_a_4323_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4323_);
lean_dec_ref_known(v___x_4321_, 1);
v_ctor_4324_ = lean_ctor_get_uint8(v_a_4319_, sizeof(void*)*12 + 2);
v___y_4225_ = v___y_4313_;
v___y_4226_ = v___y_4310_;
v___y_4227_ = v_a_4323_;
v___y_4228_ = v___y_4311_;
v___y_4229_ = v_a_4319_;
v_ctor_4230_ = v_ctor_4324_;
v___y_4231_ = v___y_4307_;
v___y_4232_ = v___y_4308_;
v___y_4233_ = v___x_4057_;
v___y_4234_ = v___y_4312_;
v___y_4235_ = v___y_4315_;
v___y_4236_ = v___y_4316_;
v___y_4237_ = v___y_4309_;
v___y_4238_ = v___y_4314_;
v___y_4239_ = v___x_4057_;
goto v___jp_4224_;
}
else
{
lean_object* v_a_4325_; uint8_t v_interpreted_4326_; 
v_a_4325_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4325_);
lean_dec_ref_known(v___x_4321_, 1);
v_interpreted_4326_ = lean_ctor_get_uint8(v_a_4325_, sizeof(void*)*12 + 1);
if (v_interpreted_4326_ == 0)
{
v___y_4173_ = v___y_4313_;
v___y_4174_ = v___y_4310_;
v___y_4175_ = v_a_4325_;
v___y_4176_ = v___y_4311_;
v___y_4177_ = v_a_4319_;
v___y_4178_ = v___y_4307_;
v___y_4179_ = v___y_4308_;
v___y_4180_ = v___x_4057_;
v___y_4181_ = v___y_4312_;
v___y_4182_ = v___y_4315_;
v___y_4183_ = v___y_4316_;
v___y_4184_ = v___y_4309_;
v___y_4185_ = v___y_4314_;
v___y_4186_ = v___x_4057_;
goto v___jp_4172_;
}
else
{
lean_object* v_self_4327_; uint8_t v_ctor_4328_; uint8_t v_heqProofs_4329_; lean_object* v_self_4330_; uint8_t v_heqProofs_4331_; uint8_t v___x_4332_; 
v_self_4327_ = lean_ctor_get(v_a_4319_, 0);
v_ctor_4328_ = lean_ctor_get_uint8(v_a_4319_, sizeof(void*)*12 + 2);
v_heqProofs_4329_ = lean_ctor_get_uint8(v_a_4319_, sizeof(void*)*12 + 4);
v_self_4330_ = lean_ctor_get(v_a_4325_, 0);
v_heqProofs_4331_ = lean_ctor_get_uint8(v_a_4325_, sizeof(void*)*12 + 4);
lean_inc_ref(v_root_4053_);
v___x_4332_ = l_Lean_Expr_isTrue(v_root_4053_);
if (v___x_4332_ == 0)
{
uint8_t v___x_4333_; 
lean_inc_ref(v_root_4054_);
v___x_4333_ = l_Lean_Expr_isTrue(v_root_4054_);
if (v___x_4333_ == 0)
{
if (v_isHEq_4032_ == 0)
{
if (v_heqProofs_4329_ == 0)
{
if (v_heqProofs_4331_ == 0)
{
v___y_4225_ = v___y_4313_;
v___y_4226_ = v___y_4310_;
v___y_4227_ = v_a_4325_;
v___y_4228_ = v___y_4311_;
v___y_4229_ = v_a_4319_;
v_ctor_4230_ = v_ctor_4328_;
v___y_4231_ = v___y_4307_;
v___y_4232_ = v___y_4308_;
v___y_4233_ = v___x_4061_;
v___y_4234_ = v___y_4312_;
v___y_4235_ = v___y_4315_;
v___y_4236_ = v___y_4316_;
v___y_4237_ = v___y_4309_;
v___y_4238_ = v___y_4314_;
v___y_4239_ = v___x_4057_;
goto v___jp_4224_;
}
else
{
lean_inc_ref(v_self_4330_);
lean_inc_ref(v_self_4327_);
v___y_4280_ = v_a_4325_;
v___y_4281_ = v___y_4307_;
v___y_4282_ = v___x_4333_;
v___y_4283_ = v_self_4330_;
v___y_4284_ = v___y_4314_;
v___y_4285_ = v___y_4315_;
v___y_4286_ = v___y_4311_;
v___y_4287_ = v___y_4309_;
v___y_4288_ = v_self_4327_;
v___y_4289_ = v___y_4308_;
v___y_4290_ = v_a_4319_;
v___y_4291_ = v___y_4313_;
v___y_4292_ = v___y_4310_;
v___y_4293_ = v___y_4316_;
v___y_4294_ = v___y_4312_;
goto v___jp_4279_;
}
}
else
{
lean_inc_ref(v_self_4330_);
lean_inc_ref(v_self_4327_);
v___y_4280_ = v_a_4325_;
v___y_4281_ = v___y_4307_;
v___y_4282_ = v___x_4333_;
v___y_4283_ = v_self_4330_;
v___y_4284_ = v___y_4314_;
v___y_4285_ = v___y_4315_;
v___y_4286_ = v___y_4311_;
v___y_4287_ = v___y_4309_;
v___y_4288_ = v_self_4327_;
v___y_4289_ = v___y_4308_;
v___y_4290_ = v_a_4319_;
v___y_4291_ = v___y_4313_;
v___y_4292_ = v___y_4310_;
v___y_4293_ = v___y_4316_;
v___y_4294_ = v___y_4312_;
goto v___jp_4279_;
}
}
else
{
lean_inc_ref(v_self_4330_);
lean_inc_ref(v_self_4327_);
v___y_4280_ = v_a_4325_;
v___y_4281_ = v___y_4307_;
v___y_4282_ = v___x_4333_;
v___y_4283_ = v_self_4330_;
v___y_4284_ = v___y_4314_;
v___y_4285_ = v___y_4315_;
v___y_4286_ = v___y_4311_;
v___y_4287_ = v___y_4309_;
v___y_4288_ = v_self_4327_;
v___y_4289_ = v___y_4308_;
v___y_4290_ = v_a_4319_;
v___y_4291_ = v___y_4313_;
v___y_4292_ = v___y_4310_;
v___y_4293_ = v___y_4316_;
v___y_4294_ = v___y_4312_;
goto v___jp_4279_;
}
}
else
{
v___y_4266_ = v___y_4307_;
v___y_4267_ = v_a_4325_;
v___y_4268_ = v___y_4314_;
v___y_4269_ = v___y_4315_;
v___y_4270_ = v___y_4311_;
v___y_4271_ = v___y_4309_;
v___y_4272_ = v___y_4308_;
v___y_4273_ = v_a_4319_;
v___y_4274_ = v___y_4313_;
v___y_4275_ = v___y_4310_;
v___y_4276_ = v___y_4316_;
v___y_4277_ = v___y_4312_;
goto v___jp_4265_;
}
}
else
{
v___y_4266_ = v___y_4307_;
v___y_4267_ = v_a_4325_;
v___y_4268_ = v___y_4314_;
v___y_4269_ = v___y_4315_;
v___y_4270_ = v___y_4311_;
v___y_4271_ = v___y_4309_;
v___y_4272_ = v___y_4308_;
v___y_4273_ = v_a_4319_;
v___y_4274_ = v___y_4313_;
v___y_4275_ = v___y_4310_;
v___y_4276_ = v___y_4316_;
v___y_4277_ = v___y_4312_;
goto v___jp_4265_;
}
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec(v_a_4319_);
lean_dec(v_a_4052_);
lean_dec(v_a_4049_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
v_a_4334_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4321_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4321_);
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
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
lean_dec(v_a_4052_);
lean_dec(v_a_4049_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
v_a_4342_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4318_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4318_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
}
else
{
lean_object* v_options_4389_; uint8_t v_hasTrace_4390_; 
lean_dec(v_a_4052_);
lean_dec(v_a_4049_);
lean_dec_ref(v_proof_4031_);
v_options_4389_ = lean_ctor_get(v_a_4041_, 1);
v_hasTrace_4390_ = lean_ctor_get_uint8(v_options_4389_, sizeof(void*)*1);
if (v_hasTrace_4390_ == 0)
{
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
goto v___jp_4044_;
}
else
{
lean_object* v_toCold_4391_; lean_object* v_inheritedTraceOptions_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; 
v_toCold_4391_ = lean_ctor_get(v_a_4041_, 0);
v_inheritedTraceOptions_4392_ = lean_ctor_get(v_toCold_4391_, 4);
v___x_4393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4395_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4392_, v_options_4389_, v___x_4394_);
if (v___x_4395_ == 0)
{
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
goto v___jp_4044_;
}
else
{
lean_object* v___x_4396_; 
v___x_4396_ = l_Lean_Meta_Grind_updateLastTag(v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v___x_4397_; 
lean_dec_ref_known(v___x_4396_, 1);
v___x_4397_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4029_, v_a_4033_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; lean_object* v___x_4399_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v___x_4397_, 1);
v___x_4399_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4030_, v_a_4033_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref_known(v___x_4399_, 1);
v___x_4401_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4402_, 0, v_a_4398_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4402_);
lean_ctor_set(v___x_4403_, 1, v_a_4400_);
v___x_4404_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4403_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
v___x_4406_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4393_, v___x_4405_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_dec_ref_known(v___x_4406_, 1);
goto v___jp_4044_;
}
else
{
return v___x_4406_;
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v_a_4398_);
v_a_4407_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4399_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4399_);
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
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec_ref(v_rhs_4030_);
v_a_4415_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4397_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4397_);
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
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
return v___x_4396_;
}
}
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v_a_4049_);
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
v_a_4423_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4051_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4051_);
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
lean_dec_ref(v_proof_4031_);
lean_dec_ref(v_rhs_4030_);
lean_dec_ref(v_lhs_4029_);
v_a_4431_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4048_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4048_);
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
v___jp_4044_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = lean_box(0);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4439_, lean_object* v_rhs_4440_, lean_object* v_proof_4441_, lean_object* v_isHEq_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_){
_start:
{
uint8_t v_isHEq_boxed_4454_; lean_object* v_res_4455_; 
v_isHEq_boxed_4454_ = lean_unbox(v_isHEq_4442_);
v_res_4455_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4439_, v_rhs_4440_, v_proof_4441_, v_isHEq_boxed_4454_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
lean_dec(v_a_4452_);
lean_dec_ref(v_a_4451_);
lean_dec(v_a_4450_);
lean_dec_ref(v_a_4449_);
lean_dec(v_a_4448_);
lean_dec_ref(v_a_4447_);
lean_dec(v_a_4446_);
lean_dec_ref(v_a_4445_);
lean_dec(v_a_4444_);
lean_dec(v_a_4443_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4458_){
_start:
{
lean_object* v___x_4460_; lean_object* v_toGoalState_4461_; lean_object* v_mvarId_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4498_; 
v___x_4460_ = lean_st_ref_take(v_a_4458_);
v_toGoalState_4461_ = lean_ctor_get(v___x_4460_, 0);
v_mvarId_4462_ = lean_ctor_get(v___x_4460_, 1);
v_isSharedCheck_4498_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4464_ = v___x_4460_;
v_isShared_4465_ = v_isSharedCheck_4498_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_mvarId_4462_);
lean_inc(v_toGoalState_4461_);
lean_dec(v___x_4460_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4498_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v_nextDeclIdx_4466_; lean_object* v_enodeMap_4467_; lean_object* v_exprs_4468_; lean_object* v_parents_4469_; lean_object* v_congrTable_4470_; lean_object* v_appMap_4471_; lean_object* v_indicesFound_4472_; uint8_t v_inconsistent_4473_; lean_object* v_nextIdx_4474_; lean_object* v_newRawFacts_4475_; lean_object* v_facts_4476_; lean_object* v_extThms_4477_; lean_object* v_ematch_4478_; lean_object* v_inj_4479_; lean_object* v_split_4480_; lean_object* v_clean_4481_; lean_object* v_sstates_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4496_; 
v_nextDeclIdx_4466_ = lean_ctor_get(v_toGoalState_4461_, 0);
v_enodeMap_4467_ = lean_ctor_get(v_toGoalState_4461_, 1);
v_exprs_4468_ = lean_ctor_get(v_toGoalState_4461_, 2);
v_parents_4469_ = lean_ctor_get(v_toGoalState_4461_, 3);
v_congrTable_4470_ = lean_ctor_get(v_toGoalState_4461_, 4);
v_appMap_4471_ = lean_ctor_get(v_toGoalState_4461_, 5);
v_indicesFound_4472_ = lean_ctor_get(v_toGoalState_4461_, 6);
v_inconsistent_4473_ = lean_ctor_get_uint8(v_toGoalState_4461_, sizeof(void*)*17);
v_nextIdx_4474_ = lean_ctor_get(v_toGoalState_4461_, 8);
v_newRawFacts_4475_ = lean_ctor_get(v_toGoalState_4461_, 9);
v_facts_4476_ = lean_ctor_get(v_toGoalState_4461_, 10);
v_extThms_4477_ = lean_ctor_get(v_toGoalState_4461_, 11);
v_ematch_4478_ = lean_ctor_get(v_toGoalState_4461_, 12);
v_inj_4479_ = lean_ctor_get(v_toGoalState_4461_, 13);
v_split_4480_ = lean_ctor_get(v_toGoalState_4461_, 14);
v_clean_4481_ = lean_ctor_get(v_toGoalState_4461_, 15);
v_sstates_4482_ = lean_ctor_get(v_toGoalState_4461_, 16);
v_isSharedCheck_4496_ = !lean_is_exclusive(v_toGoalState_4461_);
if (v_isSharedCheck_4496_ == 0)
{
lean_object* v_unused_4497_; 
v_unused_4497_ = lean_ctor_get(v_toGoalState_4461_, 7);
lean_dec(v_unused_4497_);
v___x_4484_ = v_toGoalState_4461_;
v_isShared_4485_ = v_isSharedCheck_4496_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_sstates_4482_);
lean_inc(v_clean_4481_);
lean_inc(v_split_4480_);
lean_inc(v_inj_4479_);
lean_inc(v_ematch_4478_);
lean_inc(v_extThms_4477_);
lean_inc(v_facts_4476_);
lean_inc(v_newRawFacts_4475_);
lean_inc(v_nextIdx_4474_);
lean_inc(v_indicesFound_4472_);
lean_inc(v_appMap_4471_);
lean_inc(v_congrTable_4470_);
lean_inc(v_parents_4469_);
lean_inc(v_exprs_4468_);
lean_inc(v_enodeMap_4467_);
lean_inc(v_nextDeclIdx_4466_);
lean_dec(v_toGoalState_4461_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4496_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4486_; lean_object* v___x_4488_; 
v___x_4486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 7, v___x_4486_);
v___x_4488_ = v___x_4484_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_nextDeclIdx_4466_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v_enodeMap_4467_);
lean_ctor_set(v_reuseFailAlloc_4495_, 2, v_exprs_4468_);
lean_ctor_set(v_reuseFailAlloc_4495_, 3, v_parents_4469_);
lean_ctor_set(v_reuseFailAlloc_4495_, 4, v_congrTable_4470_);
lean_ctor_set(v_reuseFailAlloc_4495_, 5, v_appMap_4471_);
lean_ctor_set(v_reuseFailAlloc_4495_, 6, v_indicesFound_4472_);
lean_ctor_set(v_reuseFailAlloc_4495_, 7, v___x_4486_);
lean_ctor_set(v_reuseFailAlloc_4495_, 8, v_nextIdx_4474_);
lean_ctor_set(v_reuseFailAlloc_4495_, 9, v_newRawFacts_4475_);
lean_ctor_set(v_reuseFailAlloc_4495_, 10, v_facts_4476_);
lean_ctor_set(v_reuseFailAlloc_4495_, 11, v_extThms_4477_);
lean_ctor_set(v_reuseFailAlloc_4495_, 12, v_ematch_4478_);
lean_ctor_set(v_reuseFailAlloc_4495_, 13, v_inj_4479_);
lean_ctor_set(v_reuseFailAlloc_4495_, 14, v_split_4480_);
lean_ctor_set(v_reuseFailAlloc_4495_, 15, v_clean_4481_);
lean_ctor_set(v_reuseFailAlloc_4495_, 16, v_sstates_4482_);
lean_ctor_set_uint8(v_reuseFailAlloc_4495_, sizeof(void*)*17, v_inconsistent_4473_);
v___x_4488_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
lean_object* v___x_4490_; 
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 0, v___x_4488_);
v___x_4490_ = v___x_4464_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4488_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v_mvarId_4462_);
v___x_4490_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4491_ = lean_st_ref_put(v_a_4458_, v___x_4490_);
v___x_4492_ = lean_box(0);
v___x_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
return v___x_4493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4499_, lean_object* v_a_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4499_);
lean_dec(v_a_4499_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_){
_start:
{
lean_object* v___x_4513_; 
v___x_4513_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4502_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
lean_dec(v_a_4515_);
lean_dec(v_a_4514_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4526_){
_start:
{
lean_object* v___x_4528_; lean_object* v_toGoalState_4529_; lean_object* v_newFacts_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; 
v___x_4528_ = lean_st_ref_get(v_a_4526_);
v_toGoalState_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc_ref(v_toGoalState_4529_);
lean_dec(v___x_4528_);
v_newFacts_4530_ = lean_ctor_get(v_toGoalState_4529_, 7);
lean_inc_ref(v_newFacts_4530_);
lean_dec_ref(v_toGoalState_4529_);
v___x_4531_ = lean_array_get_size(v_newFacts_4530_);
v___x_4532_ = lean_unsigned_to_nat(1u);
v___x_4533_ = lean_nat_sub(v___x_4531_, v___x_4532_);
v___x_4534_ = lean_nat_dec_lt(v___x_4533_, v___x_4531_);
if (v___x_4534_ == 0)
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
lean_dec(v___x_4533_);
lean_dec_ref(v_newFacts_4530_);
v___x_4535_ = lean_box(0);
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
return v___x_4536_;
}
else
{
lean_object* v___x_4537_; lean_object* v_toGoalState_4538_; lean_object* v_mvarId_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4576_; 
v___x_4537_ = lean_st_ref_take(v_a_4526_);
v_toGoalState_4538_ = lean_ctor_get(v___x_4537_, 0);
v_mvarId_4539_ = lean_ctor_get(v___x_4537_, 1);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4541_ = v___x_4537_;
v_isShared_4542_ = v_isSharedCheck_4576_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_mvarId_4539_);
lean_inc(v_toGoalState_4538_);
lean_dec(v___x_4537_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4576_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v_nextDeclIdx_4543_; lean_object* v_enodeMap_4544_; lean_object* v_exprs_4545_; lean_object* v_parents_4546_; lean_object* v_congrTable_4547_; lean_object* v_appMap_4548_; lean_object* v_indicesFound_4549_; lean_object* v_newFacts_4550_; uint8_t v_inconsistent_4551_; lean_object* v_nextIdx_4552_; lean_object* v_newRawFacts_4553_; lean_object* v_facts_4554_; lean_object* v_extThms_4555_; lean_object* v_ematch_4556_; lean_object* v_inj_4557_; lean_object* v_split_4558_; lean_object* v_clean_4559_; lean_object* v_sstates_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4575_; 
v_nextDeclIdx_4543_ = lean_ctor_get(v_toGoalState_4538_, 0);
v_enodeMap_4544_ = lean_ctor_get(v_toGoalState_4538_, 1);
v_exprs_4545_ = lean_ctor_get(v_toGoalState_4538_, 2);
v_parents_4546_ = lean_ctor_get(v_toGoalState_4538_, 3);
v_congrTable_4547_ = lean_ctor_get(v_toGoalState_4538_, 4);
v_appMap_4548_ = lean_ctor_get(v_toGoalState_4538_, 5);
v_indicesFound_4549_ = lean_ctor_get(v_toGoalState_4538_, 6);
v_newFacts_4550_ = lean_ctor_get(v_toGoalState_4538_, 7);
v_inconsistent_4551_ = lean_ctor_get_uint8(v_toGoalState_4538_, sizeof(void*)*17);
v_nextIdx_4552_ = lean_ctor_get(v_toGoalState_4538_, 8);
v_newRawFacts_4553_ = lean_ctor_get(v_toGoalState_4538_, 9);
v_facts_4554_ = lean_ctor_get(v_toGoalState_4538_, 10);
v_extThms_4555_ = lean_ctor_get(v_toGoalState_4538_, 11);
v_ematch_4556_ = lean_ctor_get(v_toGoalState_4538_, 12);
v_inj_4557_ = lean_ctor_get(v_toGoalState_4538_, 13);
v_split_4558_ = lean_ctor_get(v_toGoalState_4538_, 14);
v_clean_4559_ = lean_ctor_get(v_toGoalState_4538_, 15);
v_sstates_4560_ = lean_ctor_get(v_toGoalState_4538_, 16);
v_isSharedCheck_4575_ = !lean_is_exclusive(v_toGoalState_4538_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4562_ = v_toGoalState_4538_;
v_isShared_4563_ = v_isSharedCheck_4575_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_sstates_4560_);
lean_inc(v_clean_4559_);
lean_inc(v_split_4558_);
lean_inc(v_inj_4557_);
lean_inc(v_ematch_4556_);
lean_inc(v_extThms_4555_);
lean_inc(v_facts_4554_);
lean_inc(v_newRawFacts_4553_);
lean_inc(v_nextIdx_4552_);
lean_inc(v_newFacts_4550_);
lean_inc(v_indicesFound_4549_);
lean_inc(v_appMap_4548_);
lean_inc(v_congrTable_4547_);
lean_inc(v_parents_4546_);
lean_inc(v_exprs_4545_);
lean_inc(v_enodeMap_4544_);
lean_inc(v_nextDeclIdx_4543_);
lean_dec(v_toGoalState_4538_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4575_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4564_; lean_object* v___x_4566_; 
v___x_4564_ = lean_array_pop(v_newFacts_4550_);
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 7, v___x_4564_);
v___x_4566_ = v___x_4562_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_nextDeclIdx_4543_);
lean_ctor_set(v_reuseFailAlloc_4574_, 1, v_enodeMap_4544_);
lean_ctor_set(v_reuseFailAlloc_4574_, 2, v_exprs_4545_);
lean_ctor_set(v_reuseFailAlloc_4574_, 3, v_parents_4546_);
lean_ctor_set(v_reuseFailAlloc_4574_, 4, v_congrTable_4547_);
lean_ctor_set(v_reuseFailAlloc_4574_, 5, v_appMap_4548_);
lean_ctor_set(v_reuseFailAlloc_4574_, 6, v_indicesFound_4549_);
lean_ctor_set(v_reuseFailAlloc_4574_, 7, v___x_4564_);
lean_ctor_set(v_reuseFailAlloc_4574_, 8, v_nextIdx_4552_);
lean_ctor_set(v_reuseFailAlloc_4574_, 9, v_newRawFacts_4553_);
lean_ctor_set(v_reuseFailAlloc_4574_, 10, v_facts_4554_);
lean_ctor_set(v_reuseFailAlloc_4574_, 11, v_extThms_4555_);
lean_ctor_set(v_reuseFailAlloc_4574_, 12, v_ematch_4556_);
lean_ctor_set(v_reuseFailAlloc_4574_, 13, v_inj_4557_);
lean_ctor_set(v_reuseFailAlloc_4574_, 14, v_split_4558_);
lean_ctor_set(v_reuseFailAlloc_4574_, 15, v_clean_4559_);
lean_ctor_set(v_reuseFailAlloc_4574_, 16, v_sstates_4560_);
lean_ctor_set_uint8(v_reuseFailAlloc_4574_, sizeof(void*)*17, v_inconsistent_4551_);
v___x_4566_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
lean_object* v___x_4568_; 
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v___x_4566_);
v___x_4568_ = v___x_4541_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4566_);
lean_ctor_set(v_reuseFailAlloc_4573_, 1, v_mvarId_4539_);
v___x_4568_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4569_ = lean_st_ref_put(v_a_4526_, v___x_4568_);
v___x_4570_ = lean_array_fget(v_newFacts_4530_, v___x_4533_);
lean_dec(v___x_4533_);
lean_dec_ref(v_newFacts_4530_);
v___x_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4570_);
v___x_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4571_);
return v___x_4572_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4577_, lean_object* v_a_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4577_);
lean_dec(v_a_4577_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v___x_4591_; 
v___x_4591_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4580_);
return v___x_4591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
lean_dec(v_a_4595_);
lean_dec_ref(v_a_4594_);
lean_dec(v_a_4593_);
lean_dec(v_a_4592_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4604_, lean_object* v_rhs_4605_, lean_object* v_proof_4606_, uint8_t v_isHEq_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v___x_4619_; 
v___x_4619_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4604_, v_rhs_4605_, v_proof_4606_, v_isHEq_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_);
if (lean_obj_tag(v___x_4619_) == 0)
{
lean_object* v___x_4620_; 
lean_dec_ref_known(v___x_4619_, 1);
lean_inc(v_a_4617_);
lean_inc_ref(v_a_4616_);
lean_inc(v_a_4615_);
lean_inc_ref(v_a_4614_);
lean_inc(v_a_4613_);
lean_inc_ref(v_a_4612_);
lean_inc(v_a_4611_);
lean_inc_ref(v_a_4610_);
lean_inc(v_a_4609_);
lean_inc(v_a_4608_);
v___x_4620_ = lean_grind_process_new_facts(v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_);
return v___x_4620_;
}
else
{
return v___x_4619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4621_, lean_object* v_rhs_4622_, lean_object* v_proof_4623_, lean_object* v_isHEq_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
uint8_t v_isHEq_boxed_4636_; lean_object* v_res_4637_; 
v_isHEq_boxed_4636_ = lean_unbox(v_isHEq_4624_);
v_res_4637_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4621_, v_rhs_4622_, v_proof_4623_, v_isHEq_boxed_4636_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_);
lean_dec(v_a_4634_);
lean_dec_ref(v_a_4633_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec(v_a_4625_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4638_, lean_object* v_rhs_4639_, lean_object* v_proof_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
uint8_t v___x_4652_; lean_object* v___x_4653_; 
v___x_4652_ = 0;
v___x_4653_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4638_, v_rhs_4639_, v_proof_4640_, v___x_4652_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4654_, lean_object* v_rhs_4655_, lean_object* v_proof_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4654_, v_rhs_4655_, v_proof_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
lean_dec(v_a_4658_);
lean_dec(v_a_4657_);
return v_res_4668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4669_, lean_object* v_rhs_4670_, lean_object* v_proof_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_){
_start:
{
uint8_t v___x_4683_; lean_object* v___x_4684_; 
v___x_4683_ = 1;
v___x_4684_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4669_, v_rhs_4670_, v_proof_4671_, v___x_4683_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4685_, lean_object* v_rhs_4686_, lean_object* v_proof_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4685_, v_rhs_4686_, v_proof_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
lean_dec(v_a_4689_);
lean_dec(v_a_4688_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4700_, lean_object* v_a_4701_){
_start:
{
lean_object* v___x_4703_; lean_object* v_toGoalState_4704_; lean_object* v_mvarId_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4741_; 
v___x_4703_ = lean_st_ref_take(v_a_4701_);
v_toGoalState_4704_ = lean_ctor_get(v___x_4703_, 0);
v_mvarId_4705_ = lean_ctor_get(v___x_4703_, 1);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4707_ = v___x_4703_;
v_isShared_4708_ = v_isSharedCheck_4741_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_mvarId_4705_);
lean_inc(v_toGoalState_4704_);
lean_dec(v___x_4703_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4741_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v_nextDeclIdx_4709_; lean_object* v_enodeMap_4710_; lean_object* v_exprs_4711_; lean_object* v_parents_4712_; lean_object* v_congrTable_4713_; lean_object* v_appMap_4714_; lean_object* v_indicesFound_4715_; lean_object* v_newFacts_4716_; uint8_t v_inconsistent_4717_; lean_object* v_nextIdx_4718_; lean_object* v_newRawFacts_4719_; lean_object* v_facts_4720_; lean_object* v_extThms_4721_; lean_object* v_ematch_4722_; lean_object* v_inj_4723_; lean_object* v_split_4724_; lean_object* v_clean_4725_; lean_object* v_sstates_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4740_; 
v_nextDeclIdx_4709_ = lean_ctor_get(v_toGoalState_4704_, 0);
v_enodeMap_4710_ = lean_ctor_get(v_toGoalState_4704_, 1);
v_exprs_4711_ = lean_ctor_get(v_toGoalState_4704_, 2);
v_parents_4712_ = lean_ctor_get(v_toGoalState_4704_, 3);
v_congrTable_4713_ = lean_ctor_get(v_toGoalState_4704_, 4);
v_appMap_4714_ = lean_ctor_get(v_toGoalState_4704_, 5);
v_indicesFound_4715_ = lean_ctor_get(v_toGoalState_4704_, 6);
v_newFacts_4716_ = lean_ctor_get(v_toGoalState_4704_, 7);
v_inconsistent_4717_ = lean_ctor_get_uint8(v_toGoalState_4704_, sizeof(void*)*17);
v_nextIdx_4718_ = lean_ctor_get(v_toGoalState_4704_, 8);
v_newRawFacts_4719_ = lean_ctor_get(v_toGoalState_4704_, 9);
v_facts_4720_ = lean_ctor_get(v_toGoalState_4704_, 10);
v_extThms_4721_ = lean_ctor_get(v_toGoalState_4704_, 11);
v_ematch_4722_ = lean_ctor_get(v_toGoalState_4704_, 12);
v_inj_4723_ = lean_ctor_get(v_toGoalState_4704_, 13);
v_split_4724_ = lean_ctor_get(v_toGoalState_4704_, 14);
v_clean_4725_ = lean_ctor_get(v_toGoalState_4704_, 15);
v_sstates_4726_ = lean_ctor_get(v_toGoalState_4704_, 16);
v_isSharedCheck_4740_ = !lean_is_exclusive(v_toGoalState_4704_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4728_ = v_toGoalState_4704_;
v_isShared_4729_ = v_isSharedCheck_4740_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_sstates_4726_);
lean_inc(v_clean_4725_);
lean_inc(v_split_4724_);
lean_inc(v_inj_4723_);
lean_inc(v_ematch_4722_);
lean_inc(v_extThms_4721_);
lean_inc(v_facts_4720_);
lean_inc(v_newRawFacts_4719_);
lean_inc(v_nextIdx_4718_);
lean_inc(v_newFacts_4716_);
lean_inc(v_indicesFound_4715_);
lean_inc(v_appMap_4714_);
lean_inc(v_congrTable_4713_);
lean_inc(v_parents_4712_);
lean_inc(v_exprs_4711_);
lean_inc(v_enodeMap_4710_);
lean_inc(v_nextDeclIdx_4709_);
lean_dec(v_toGoalState_4704_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4740_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4730_; lean_object* v___x_4732_; 
v___x_4730_ = l_Lean_PersistentArray_push___redArg(v_facts_4720_, v_fact_4700_);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 10, v___x_4730_);
v___x_4732_ = v___x_4728_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_nextDeclIdx_4709_);
lean_ctor_set(v_reuseFailAlloc_4739_, 1, v_enodeMap_4710_);
lean_ctor_set(v_reuseFailAlloc_4739_, 2, v_exprs_4711_);
lean_ctor_set(v_reuseFailAlloc_4739_, 3, v_parents_4712_);
lean_ctor_set(v_reuseFailAlloc_4739_, 4, v_congrTable_4713_);
lean_ctor_set(v_reuseFailAlloc_4739_, 5, v_appMap_4714_);
lean_ctor_set(v_reuseFailAlloc_4739_, 6, v_indicesFound_4715_);
lean_ctor_set(v_reuseFailAlloc_4739_, 7, v_newFacts_4716_);
lean_ctor_set(v_reuseFailAlloc_4739_, 8, v_nextIdx_4718_);
lean_ctor_set(v_reuseFailAlloc_4739_, 9, v_newRawFacts_4719_);
lean_ctor_set(v_reuseFailAlloc_4739_, 10, v___x_4730_);
lean_ctor_set(v_reuseFailAlloc_4739_, 11, v_extThms_4721_);
lean_ctor_set(v_reuseFailAlloc_4739_, 12, v_ematch_4722_);
lean_ctor_set(v_reuseFailAlloc_4739_, 13, v_inj_4723_);
lean_ctor_set(v_reuseFailAlloc_4739_, 14, v_split_4724_);
lean_ctor_set(v_reuseFailAlloc_4739_, 15, v_clean_4725_);
lean_ctor_set(v_reuseFailAlloc_4739_, 16, v_sstates_4726_);
lean_ctor_set_uint8(v_reuseFailAlloc_4739_, sizeof(void*)*17, v_inconsistent_4717_);
v___x_4732_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
lean_object* v___x_4734_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 0, v___x_4732_);
v___x_4734_ = v___x_4707_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v___x_4732_);
lean_ctor_set(v_reuseFailAlloc_4738_, 1, v_mvarId_4705_);
v___x_4734_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4735_ = lean_st_ref_put(v_a_4701_, v___x_4734_);
v___x_4736_ = lean_box(0);
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
return v___x_4737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4742_, v_a_4743_);
lean_dec(v_a_4743_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v___x_4758_; 
v___x_4758_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4746_, v_a_4747_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec(v_a_4761_);
lean_dec(v_a_4760_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4772_, lean_object* v_rhs_4773_, lean_object* v_proof_4774_, lean_object* v_generation_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v___x_4787_; 
lean_inc_ref(v_rhs_4773_);
lean_inc_ref(v_lhs_4772_);
v___x_4787_ = l_Lean_Meta_mkEq(v_lhs_4772_, v_rhs_4773_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v___x_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4799_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc_n(v_a_4788_, 2);
lean_dec_ref_known(v___x_4787_, 1);
v___x_4789_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4788_, v_a_4776_);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4799_ == 0)
{
lean_object* v_unused_4800_; 
v_unused_4800_ = lean_ctor_get(v___x_4789_, 0);
lean_dec(v_unused_4800_);
v___x_4791_ = v___x_4789_;
v_isShared_4792_ = v_isSharedCheck_4799_;
goto v_resetjp_4790_;
}
else
{
lean_dec(v___x_4789_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4799_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4794_; 
if (v_isShared_4792_ == 0)
{
lean_ctor_set_tag(v___x_4791_, 1);
lean_ctor_set(v___x_4791_, 0, v_a_4788_);
v___x_4794_ = v___x_4791_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4788_);
v___x_4794_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
lean_object* v___x_4795_; 
lean_inc(v_a_4785_);
lean_inc_ref(v_a_4784_);
lean_inc(v_a_4783_);
lean_inc_ref(v_a_4782_);
lean_inc(v_a_4781_);
lean_inc_ref(v_a_4780_);
lean_inc(v_a_4779_);
lean_inc_ref(v_a_4778_);
lean_inc(v_a_4777_);
lean_inc(v_a_4776_);
lean_inc_ref(v___x_4794_);
lean_inc(v_generation_4775_);
lean_inc_ref(v_lhs_4772_);
v___x_4795_ = lean_grind_internalize(v_lhs_4772_, v_generation_4775_, v___x_4794_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v___x_4796_; 
lean_dec_ref_known(v___x_4795_, 1);
lean_inc(v_a_4785_);
lean_inc_ref(v_a_4784_);
lean_inc(v_a_4783_);
lean_inc_ref(v_a_4782_);
lean_inc(v_a_4781_);
lean_inc_ref(v_a_4780_);
lean_inc(v_a_4779_);
lean_inc_ref(v_a_4778_);
lean_inc(v_a_4777_);
lean_inc(v_a_4776_);
lean_inc_ref(v_rhs_4773_);
v___x_4796_ = lean_grind_internalize(v_rhs_4773_, v_generation_4775_, v___x_4794_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v___x_4797_; 
lean_dec_ref_known(v___x_4796_, 1);
v___x_4797_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4772_, v_rhs_4773_, v_proof_4774_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
return v___x_4797_;
}
else
{
lean_dec_ref(v_proof_4774_);
lean_dec_ref(v_rhs_4773_);
lean_dec_ref(v_lhs_4772_);
return v___x_4796_;
}
}
else
{
lean_dec_ref(v___x_4794_);
lean_dec(v_generation_4775_);
lean_dec_ref(v_proof_4774_);
lean_dec_ref(v_rhs_4773_);
lean_dec_ref(v_lhs_4772_);
return v___x_4795_;
}
}
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4808_; 
lean_dec(v_generation_4775_);
lean_dec_ref(v_proof_4774_);
lean_dec_ref(v_rhs_4773_);
lean_dec_ref(v_lhs_4772_);
v_a_4801_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4803_ = v___x_4787_;
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4787_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4808_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___x_4806_; 
if (v_isShared_4804_ == 0)
{
v___x_4806_ = v___x_4803_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4809_, lean_object* v_rhs_4810_, lean_object* v_proof_4811_, lean_object* v_generation_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_){
_start:
{
lean_object* v_res_4824_; 
v_res_4824_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4809_, v_rhs_4810_, v_proof_4811_, v_generation_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_);
lean_dec(v_a_4822_);
lean_dec_ref(v_a_4821_);
lean_dec(v_a_4820_);
lean_dec_ref(v_a_4819_);
lean_dec(v_a_4818_);
lean_dec_ref(v_a_4817_);
lean_dec(v_a_4816_);
lean_dec_ref(v_a_4815_);
lean_dec(v_a_4814_);
lean_dec(v_a_4813_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4825_, lean_object* v_generation_4826_, lean_object* v_p_4827_, uint8_t v_isNeg_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4840_ = lean_box(0);
lean_inc(v_a_4838_);
lean_inc_ref(v_a_4837_);
lean_inc(v_a_4836_);
lean_inc_ref(v_a_4835_);
lean_inc(v_a_4834_);
lean_inc_ref(v_a_4833_);
lean_inc(v_a_4832_);
lean_inc_ref(v_a_4831_);
lean_inc(v_a_4830_);
lean_inc(v_a_4829_);
lean_inc_ref(v_p_4827_);
v___x_4841_ = lean_grind_internalize(v_p_4827_, v_generation_4826_, v___x_4840_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_dec_ref_known(v___x_4841_, 1);
if (v_isNeg_4828_ == 0)
{
lean_object* v___x_4842_; 
v___x_4842_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4833_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v_a_4843_; lean_object* v___x_4844_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
lean_inc(v_a_4843_);
lean_dec_ref_known(v___x_4842_, 1);
v___x_4844_ = l_Lean_Meta_mkEqTrue(v_proof_4825_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v___x_4846_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
lean_inc(v_a_4845_);
lean_dec_ref_known(v___x_4844_, 1);
v___x_4846_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4827_, v_a_4843_, v_a_4845_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
return v___x_4846_;
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
lean_dec(v_a_4843_);
lean_dec_ref(v_p_4827_);
v_a_4847_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4844_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4844_);
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
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4862_; 
lean_dec_ref(v_p_4827_);
lean_dec_ref(v_proof_4825_);
v_a_4855_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4857_ = v___x_4842_;
v_isShared_4858_ = v_isSharedCheck_4862_;
goto v_resetjp_4856_;
}
else
{
lean_inc(v_a_4855_);
lean_dec(v___x_4842_);
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
lean_object* v___x_4863_; 
v___x_4863_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4833_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4865_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v___x_4865_ = l_Lean_Meta_mkEqFalse(v_proof_4825_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v_a_4866_; lean_object* v___x_4867_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
lean_inc(v_a_4866_);
lean_dec_ref_known(v___x_4865_, 1);
v___x_4867_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4827_, v_a_4864_, v_a_4866_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
return v___x_4867_;
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
lean_dec(v_a_4864_);
lean_dec_ref(v_p_4827_);
v_a_4868_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4865_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4865_);
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
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
lean_dec_ref(v_p_4827_);
lean_dec_ref(v_proof_4825_);
v_a_4876_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4863_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4863_);
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
}
else
{
lean_dec_ref(v_p_4827_);
lean_dec_ref(v_proof_4825_);
return v___x_4841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4884_, lean_object* v_generation_4885_, lean_object* v_p_4886_, lean_object* v_isNeg_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_){
_start:
{
uint8_t v_isNeg_boxed_4899_; lean_object* v_res_4900_; 
v_isNeg_boxed_4899_ = lean_unbox(v_isNeg_4887_);
v_res_4900_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4884_, v_generation_4885_, v_p_4886_, v_isNeg_boxed_4899_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_);
lean_dec(v_a_4897_);
lean_dec_ref(v_a_4896_);
lean_dec(v_a_4895_);
lean_dec_ref(v_a_4894_);
lean_dec(v_a_4893_);
lean_dec_ref(v_a_4892_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
lean_dec(v_a_4889_);
lean_dec(v_a_4888_);
return v_res_4900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4901_, lean_object* v_generation_4902_, lean_object* v_p_4903_, lean_object* v_lhs_4904_, lean_object* v_rhs_4905_, uint8_t v_isNeg_4906_, uint8_t v_isHEq_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_){
_start:
{
if (v_isNeg_4906_ == 0)
{
lean_object* v___x_4919_; lean_object* v___x_4920_; 
lean_inc_ref(v_p_4903_);
v___x_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4919_, 0, v_p_4903_);
lean_inc(v_a_4917_);
lean_inc_ref(v_a_4916_);
lean_inc(v_a_4915_);
lean_inc_ref(v_a_4914_);
lean_inc(v_a_4913_);
lean_inc_ref(v_a_4912_);
lean_inc(v_a_4911_);
lean_inc_ref(v_a_4910_);
lean_inc(v_a_4909_);
lean_inc(v_a_4908_);
lean_inc_ref(v___x_4919_);
lean_inc(v_generation_4902_);
lean_inc_ref(v_lhs_4904_);
v___x_4920_ = lean_grind_internalize(v_lhs_4904_, v_generation_4902_, v___x_4919_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v___x_4921_; 
lean_dec_ref_known(v___x_4920_, 1);
lean_inc(v_a_4917_);
lean_inc_ref(v_a_4916_);
lean_inc(v_a_4915_);
lean_inc_ref(v_a_4914_);
lean_inc(v_a_4913_);
lean_inc_ref(v_a_4912_);
lean_inc(v_a_4911_);
lean_inc_ref(v_a_4910_);
lean_inc(v_a_4909_);
lean_inc(v_a_4908_);
lean_inc_ref(v_rhs_4905_);
v___x_4921_ = lean_grind_internalize(v_rhs_4905_, v_generation_4902_, v___x_4919_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v___x_4922_; lean_object* v___x_4923_; 
lean_dec_ref_known(v___x_4921_, 1);
v___x_4922_ = lean_box(0);
v___x_4923_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4903_, v___x_4922_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v___x_4924_; 
lean_dec_ref_known(v___x_4923_, 1);
v___x_4924_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4904_, v_rhs_4905_, v_proof_4901_, v_isHEq_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
return v___x_4924_;
}
else
{
lean_dec_ref(v_rhs_4905_);
lean_dec_ref(v_lhs_4904_);
lean_dec_ref(v_proof_4901_);
return v___x_4923_;
}
}
else
{
lean_dec_ref(v_rhs_4905_);
lean_dec_ref(v_lhs_4904_);
lean_dec_ref(v_p_4903_);
lean_dec_ref(v_proof_4901_);
return v___x_4921_;
}
}
else
{
lean_dec_ref_known(v___x_4919_, 1);
lean_dec_ref(v_rhs_4905_);
lean_dec_ref(v_lhs_4904_);
lean_dec_ref(v_p_4903_);
lean_dec(v_generation_4902_);
lean_dec_ref(v_proof_4901_);
return v___x_4920_;
}
}
else
{
lean_object* v___x_4925_; lean_object* v___x_4926_; 
lean_dec_ref(v_rhs_4905_);
lean_dec_ref(v_lhs_4904_);
v___x_4925_ = lean_box(0);
lean_inc(v_a_4917_);
lean_inc_ref(v_a_4916_);
lean_inc(v_a_4915_);
lean_inc_ref(v_a_4914_);
lean_inc(v_a_4913_);
lean_inc_ref(v_a_4912_);
lean_inc(v_a_4911_);
lean_inc_ref(v_a_4910_);
lean_inc(v_a_4909_);
lean_inc(v_a_4908_);
lean_inc_ref(v_p_4903_);
v___x_4926_ = lean_grind_internalize(v_p_4903_, v_generation_4902_, v___x_4925_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v___x_4927_; 
lean_dec_ref_known(v___x_4926_, 1);
v___x_4927_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4912_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4929_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
lean_inc(v_a_4928_);
lean_dec_ref_known(v___x_4927_, 1);
v___x_4929_ = l_Lean_Meta_mkEqFalse(v_proof_4901_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4931_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_a_4930_);
lean_dec_ref_known(v___x_4929_, 1);
v___x_4931_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4903_, v_a_4928_, v_a_4930_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
return v___x_4931_;
}
else
{
lean_object* v_a_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4939_; 
lean_dec(v_a_4928_);
lean_dec_ref(v_p_4903_);
v_a_4932_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4934_ = v___x_4929_;
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_a_4932_);
lean_dec(v___x_4929_);
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
lean_object* v_a_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
lean_dec_ref(v_p_4903_);
lean_dec_ref(v_proof_4901_);
v_a_4940_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4942_ = v___x_4927_;
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_a_4940_);
lean_dec(v___x_4927_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4940_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
}
else
{
lean_dec_ref(v_p_4903_);
lean_dec_ref(v_proof_4901_);
return v___x_4926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4948_ = _args[0];
lean_object* v_generation_4949_ = _args[1];
lean_object* v_p_4950_ = _args[2];
lean_object* v_lhs_4951_ = _args[3];
lean_object* v_rhs_4952_ = _args[4];
lean_object* v_isNeg_4953_ = _args[5];
lean_object* v_isHEq_4954_ = _args[6];
lean_object* v_a_4955_ = _args[7];
lean_object* v_a_4956_ = _args[8];
lean_object* v_a_4957_ = _args[9];
lean_object* v_a_4958_ = _args[10];
lean_object* v_a_4959_ = _args[11];
lean_object* v_a_4960_ = _args[12];
lean_object* v_a_4961_ = _args[13];
lean_object* v_a_4962_ = _args[14];
lean_object* v_a_4963_ = _args[15];
lean_object* v_a_4964_ = _args[16];
lean_object* v_a_4965_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4966_; uint8_t v_isHEq_boxed_4967_; lean_object* v_res_4968_; 
v_isNeg_boxed_4966_ = lean_unbox(v_isNeg_4953_);
v_isHEq_boxed_4967_ = lean_unbox(v_isHEq_4954_);
v_res_4968_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4948_, v_generation_4949_, v_p_4950_, v_lhs_4951_, v_rhs_4952_, v_isNeg_boxed_4966_, v_isHEq_boxed_4967_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_);
lean_dec(v_a_4964_);
lean_dec_ref(v_a_4963_);
lean_dec(v_a_4962_);
lean_dec_ref(v_a_4961_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v_a_4956_);
lean_dec(v_a_4955_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4972_, lean_object* v_generation_4973_, lean_object* v_p_4974_, uint8_t v_isNeg_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_){
_start:
{
lean_object* v___x_4987_; 
lean_inc_ref(v_p_4974_);
v___x_4987_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4974_, v_a_4983_);
if (lean_obj_tag(v___x_4987_) == 0)
{
lean_object* v_a_4988_; lean_object* v___x_4989_; uint8_t v___x_4990_; 
v_a_4988_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_a_4988_);
lean_dec_ref_known(v___x_4987_, 1);
v___x_4989_ = l_Lean_Expr_cleanupAnnotations(v_a_4988_);
v___x_4990_ = l_Lean_Expr_isApp(v___x_4989_);
if (v___x_4990_ == 0)
{
lean_object* v___x_4991_; 
lean_dec_ref(v___x_4989_);
v___x_4991_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4972_, v_generation_4973_, v_p_4974_, v_isNeg_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
return v___x_4991_;
}
else
{
lean_object* v_arg_4992_; lean_object* v___x_4993_; uint8_t v___x_4994_; 
v_arg_4992_ = lean_ctor_get(v___x_4989_, 1);
lean_inc_ref(v_arg_4992_);
v___x_4993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4989_);
v___x_4994_ = l_Lean_Expr_isApp(v___x_4993_);
if (v___x_4994_ == 0)
{
lean_object* v___x_4995_; 
lean_dec_ref(v___x_4993_);
lean_dec_ref(v_arg_4992_);
v___x_4995_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4972_, v_generation_4973_, v_p_4974_, v_isNeg_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
return v___x_4995_;
}
else
{
lean_object* v_arg_4996_; lean_object* v___x_4997_; uint8_t v___x_4998_; 
v_arg_4996_ = lean_ctor_get(v___x_4993_, 1);
lean_inc_ref(v_arg_4996_);
v___x_4997_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4993_);
v___x_4998_ = l_Lean_Expr_isApp(v___x_4997_);
if (v___x_4998_ == 0)
{
lean_object* v___x_4999_; 
lean_dec_ref(v___x_4997_);
lean_dec_ref(v_arg_4996_);
lean_dec_ref(v_arg_4992_);
v___x_4999_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4972_, v_generation_4973_, v_p_4974_, v_isNeg_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
return v___x_4999_;
}
else
{
lean_object* v_arg_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; uint8_t v___x_5003_; 
v_arg_5000_ = lean_ctor_get(v___x_4997_, 1);
lean_inc_ref(v_arg_5000_);
v___x_5001_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4997_);
v___x_5002_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_5003_ = l_Lean_Expr_isConstOf(v___x_5001_, v___x_5002_);
if (v___x_5003_ == 0)
{
uint8_t v___x_5004_; 
lean_dec_ref(v_arg_4996_);
v___x_5004_ = l_Lean_Expr_isApp(v___x_5001_);
if (v___x_5004_ == 0)
{
lean_object* v___x_5005_; 
lean_dec_ref(v___x_5001_);
lean_dec_ref(v_arg_5000_);
lean_dec_ref(v_arg_4992_);
v___x_5005_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4972_, v_generation_4973_, v_p_4974_, v_isNeg_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
return v___x_5005_;
}
else
{
lean_object* v___x_5006_; lean_object* v___x_5007_; uint8_t v___x_5008_; 
v___x_5006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5001_);
v___x_5007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_5008_ = l_Lean_Expr_isConstOf(v___x_5006_, v___x_5007_);
lean_dec_ref(v___x_5006_);
if (v___x_5008_ == 0)
{
lean_object* v___x_5009_; 
lean_dec_ref(v_arg_5000_);
lean_dec_ref(v_arg_4992_);
v___x_5009_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4972_, v_generation_4973_, v_p_4974_, v_isNeg_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
return v___x_5009_;
}
else
{
lean_object* v___x_5010_; 
v___x_5010_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4972_, v_generation_4973_, v_p_4974_, v_arg_5000_, v_arg_4992_, v_isNeg_4975_, v___x_5008_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
return v___x_5010_;
}
}
}
else
{
uint8_t v___x_5011_; 
lean_dec_ref(v___x_5001_);
v___x_5011_ = l_Lean_Expr_isProp(v_arg_5000_);
lean_dec_ref(v_arg_5000_);
if (v___x_5011_ == 0)
{
lean_object* v___x_5012_; 
v___x_5012_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4972_, v_generation_4973_, v_p_4974_, v_arg_4996_, v_arg_4992_, v_isNeg_4975_, v___x_5011_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
return v___x_5012_;
}
else
{
lean_object* v___x_5013_; 
lean_dec_ref(v_arg_4996_);
lean_dec_ref(v_arg_4992_);
v___x_5013_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4972_, v_generation_4973_, v_p_4974_, v_isNeg_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
return v___x_5013_;
}
}
}
}
}
}
else
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
lean_dec_ref(v_p_4974_);
lean_dec(v_generation_4973_);
lean_dec_ref(v_proof_4972_);
v_a_5014_ = lean_ctor_get(v___x_4987_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_4987_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_4987_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_4987_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5022_, lean_object* v_generation_5023_, lean_object* v_p_5024_, lean_object* v_isNeg_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_){
_start:
{
uint8_t v_isNeg_boxed_5037_; lean_object* v_res_5038_; 
v_isNeg_boxed_5037_ = lean_unbox(v_isNeg_5025_);
v_res_5038_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5022_, v_generation_5023_, v_p_5024_, v_isNeg_boxed_5037_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_);
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
return v_res_5038_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5047_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5048_ = l_Lean_Name_append(v___x_5047_, v___x_5046_);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5049_, lean_object* v_proof_5050_, lean_object* v_generation_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v___y_5064_; lean_object* v___y_5065_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v___y_5077_; lean_object* v___y_5078_; lean_object* v___y_5079_; lean_object* v___y_5080_; lean_object* v___y_5081_; lean_object* v___y_5082_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v___y_5086_; lean_object* v___x_5094_; lean_object* v_options_5095_; uint8_t v_hasTrace_5096_; 
lean_inc_ref(v_fact_5049_);
v___x_5094_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5049_, v_a_5052_);
lean_dec_ref(v___x_5094_);
v_options_5095_ = lean_ctor_get(v_a_5060_, 1);
v_hasTrace_5096_ = lean_ctor_get_uint8(v_options_5095_, sizeof(void*)*1);
if (v_hasTrace_5096_ == 0)
{
v___y_5077_ = v_a_5052_;
v___y_5078_ = v_a_5053_;
v___y_5079_ = v_a_5054_;
v___y_5080_ = v_a_5055_;
v___y_5081_ = v_a_5056_;
v___y_5082_ = v_a_5057_;
v___y_5083_ = v_a_5058_;
v___y_5084_ = v_a_5059_;
v___y_5085_ = v_a_5060_;
v___y_5086_ = v_a_5061_;
goto v___jp_5076_;
}
else
{
lean_object* v_toCold_5097_; lean_object* v_inheritedTraceOptions_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; uint8_t v___x_5101_; 
v_toCold_5097_ = lean_ctor_get(v_a_5060_, 0);
v_inheritedTraceOptions_5098_ = lean_ctor_get(v_toCold_5097_, 4);
v___x_5099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5101_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5098_, v_options_5095_, v___x_5100_);
if (v___x_5101_ == 0)
{
v___y_5077_ = v_a_5052_;
v___y_5078_ = v_a_5053_;
v___y_5079_ = v_a_5054_;
v___y_5080_ = v_a_5055_;
v___y_5081_ = v_a_5056_;
v___y_5082_ = v_a_5057_;
v___y_5083_ = v_a_5058_;
v___y_5084_ = v_a_5059_;
v___y_5085_ = v_a_5060_;
v___y_5086_ = v_a_5061_;
goto v___jp_5076_;
}
else
{
lean_object* v___x_5102_; 
v___x_5102_ = l_Lean_Meta_Grind_updateLastTag(v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v___x_5103_; lean_object* v___x_5104_; 
lean_dec_ref_known(v___x_5102_, 1);
lean_inc_ref(v_fact_5049_);
v___x_5103_ = l_Lean_MessageData_ofExpr(v_fact_5049_);
v___x_5104_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5099_, v___x_5103_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_dec_ref_known(v___x_5104_, 1);
v___y_5077_ = v_a_5052_;
v___y_5078_ = v_a_5053_;
v___y_5079_ = v_a_5054_;
v___y_5080_ = v_a_5055_;
v___y_5081_ = v_a_5056_;
v___y_5082_ = v_a_5057_;
v___y_5083_ = v_a_5058_;
v___y_5084_ = v_a_5059_;
v___y_5085_ = v_a_5060_;
v___y_5086_ = v_a_5061_;
goto v___jp_5076_;
}
else
{
lean_dec(v_generation_5051_);
lean_dec_ref(v_proof_5050_);
lean_dec_ref(v_fact_5049_);
return v___x_5104_;
}
}
else
{
lean_dec(v_generation_5051_);
lean_dec_ref(v_proof_5050_);
lean_dec_ref(v_fact_5049_);
return v___x_5102_;
}
}
}
v___jp_5063_:
{
uint8_t v___x_5074_; lean_object* v___x_5075_; 
v___x_5074_ = 0;
v___x_5075_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5050_, v_generation_5051_, v_fact_5049_, v___x_5074_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
return v___x_5075_;
}
v___jp_5076_:
{
lean_object* v___x_5087_; uint8_t v___x_5088_; 
lean_inc_ref(v_fact_5049_);
v___x_5087_ = l_Lean_Expr_cleanupAnnotations(v_fact_5049_);
v___x_5088_ = l_Lean_Expr_isApp(v___x_5087_);
if (v___x_5088_ == 0)
{
lean_dec_ref(v___x_5087_);
v___y_5064_ = v___y_5077_;
v___y_5065_ = v___y_5078_;
v___y_5066_ = v___y_5079_;
v___y_5067_ = v___y_5080_;
v___y_5068_ = v___y_5081_;
v___y_5069_ = v___y_5082_;
v___y_5070_ = v___y_5083_;
v___y_5071_ = v___y_5084_;
v___y_5072_ = v___y_5085_;
v___y_5073_ = v___y_5086_;
goto v___jp_5063_;
}
else
{
lean_object* v_arg_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; uint8_t v___x_5092_; 
v_arg_5089_ = lean_ctor_get(v___x_5087_, 1);
lean_inc_ref(v_arg_5089_);
v___x_5090_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5087_);
v___x_5091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5092_ = l_Lean_Expr_isConstOf(v___x_5090_, v___x_5091_);
lean_dec_ref(v___x_5090_);
if (v___x_5092_ == 0)
{
lean_dec_ref(v_arg_5089_);
v___y_5064_ = v___y_5077_;
v___y_5065_ = v___y_5078_;
v___y_5066_ = v___y_5079_;
v___y_5067_ = v___y_5080_;
v___y_5068_ = v___y_5081_;
v___y_5069_ = v___y_5082_;
v___y_5070_ = v___y_5083_;
v___y_5071_ = v___y_5084_;
v___y_5072_ = v___y_5085_;
v___y_5073_ = v___y_5086_;
goto v___jp_5063_;
}
else
{
lean_object* v___x_5093_; 
lean_dec_ref(v_fact_5049_);
v___x_5093_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5050_, v_generation_5051_, v_arg_5089_, v___x_5092_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_);
return v___x_5093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___boxed(lean_object* v_fact_5105_, lean_object* v_proof_5106_, lean_object* v_generation_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5105_, v_proof_5106_, v_generation_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_, v_a_5112_, v_a_5113_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_);
lean_dec(v_a_5117_);
lean_dec_ref(v_a_5116_);
lean_dec(v_a_5115_);
lean_dec_ref(v_a_5114_);
lean_dec(v_a_5113_);
lean_dec_ref(v_a_5112_);
lean_dec(v_a_5111_);
lean_dec_ref(v_a_5110_);
lean_dec(v_a_5109_);
lean_dec(v_a_5108_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_5123_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; uint8_t v___x_5136_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5134_, 1);
v___x_5136_ = lean_unbox(v_a_5135_);
lean_dec(v_a_5135_);
if (v___x_5136_ == 0)
{
lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5137_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__0));
v___x_5138_ = l_Lean_Core_checkSystem(v___x_5137_, v___y_5131_, v___y_5132_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v___x_5139_; 
lean_dec_ref_known(v___x_5138_, 1);
v___x_5139_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v___y_5123_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5176_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5142_ = v___x_5139_;
v_isShared_5143_ = v_isSharedCheck_5176_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v___x_5139_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5176_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
if (lean_obj_tag(v_a_5140_) == 1)
{
lean_object* v_val_5144_; 
lean_del_object(v___x_5142_);
v_val_5144_ = lean_ctor_get(v_a_5140_, 0);
lean_inc(v_val_5144_);
lean_dec_ref_known(v_a_5140_, 1);
if (lean_obj_tag(v_val_5144_) == 0)
{
lean_object* v_lhs_5145_; lean_object* v_rhs_5146_; lean_object* v_proof_5147_; uint8_t v_isHEq_5148_; lean_object* v___x_5149_; 
v_lhs_5145_ = lean_ctor_get(v_val_5144_, 0);
lean_inc_ref(v_lhs_5145_);
v_rhs_5146_ = lean_ctor_get(v_val_5144_, 1);
lean_inc_ref(v_rhs_5146_);
v_proof_5147_ = lean_ctor_get(v_val_5144_, 2);
lean_inc_ref(v_proof_5147_);
v_isHEq_5148_ = lean_ctor_get_uint8(v_val_5144_, sizeof(void*)*3);
lean_dec_ref_known(v_val_5144_, 3);
v___x_5149_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_5145_, v_rhs_5146_, v_proof_5147_, v_isHEq_5148_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_);
if (lean_obj_tag(v___x_5149_) == 0)
{
lean_dec_ref_known(v___x_5149_, 1);
goto _start;
}
else
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5158_; 
v_a_5151_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5153_ = v___x_5149_;
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v___x_5149_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5156_; 
if (v_isShared_5154_ == 0)
{
v___x_5156_ = v___x_5153_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5151_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
}
else
{
lean_object* v_prop_5159_; lean_object* v_proof_5160_; lean_object* v_generation_5161_; lean_object* v___x_5162_; 
v_prop_5159_ = lean_ctor_get(v_val_5144_, 0);
lean_inc_ref(v_prop_5159_);
v_proof_5160_ = lean_ctor_get(v_val_5144_, 1);
lean_inc_ref(v_proof_5160_);
v_generation_5161_ = lean_ctor_get(v_val_5144_, 2);
lean_inc(v_generation_5161_);
lean_dec_ref_known(v_val_5144_, 3);
v___x_5162_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_prop_5159_, v_proof_5160_, v_generation_5161_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_dec_ref_known(v___x_5162_, 1);
goto _start;
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
v_a_5164_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5162_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5162_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
}
else
{
lean_object* v___x_5172_; lean_object* v___x_5174_; 
lean_dec(v_a_5140_);
v___x_5172_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5143_ == 0)
{
lean_ctor_set(v___x_5142_, 0, v___x_5172_);
v___x_5174_ = v___x_5142_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5172_);
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
v_a_5177_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5179_ = v___x_5139_;
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_a_5177_);
lean_dec(v___x_5139_);
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
lean_object* v_a_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5192_; 
v_a_5185_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5187_ = v___x_5138_;
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_a_5185_);
lean_dec(v___x_5138_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5190_; 
if (v_isShared_5188_ == 0)
{
v___x_5190_ = v___x_5187_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_a_5185_);
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
lean_object* v___x_5193_; 
v___x_5193_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v___y_5123_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5201_; 
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5201_ == 0)
{
lean_object* v_unused_5202_; 
v_unused_5202_ = lean_ctor_get(v___x_5193_, 0);
lean_dec(v_unused_5202_);
v___x_5195_ = v___x_5193_;
v_isShared_5196_ = v_isSharedCheck_5201_;
goto v_resetjp_5194_;
}
else
{
lean_dec(v___x_5193_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5201_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5197_; lean_object* v___x_5199_; 
v___x_5197_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___closed__0));
if (v_isShared_5196_ == 0)
{
lean_ctor_set(v___x_5195_, 0, v___x_5197_);
v___x_5199_ = v___x_5195_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v___x_5197_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
else
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5210_; 
v_a_5203_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5205_ = v___x_5193_;
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___x_5193_);
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
else
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
v_a_5211_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5134_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5134_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg___boxed(lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_);
lean_dec(v___y_5228_);
lean_dec_ref(v___y_5227_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
lean_dec(v___y_5222_);
lean_dec_ref(v___y_5221_);
lean_dec(v___y_5220_);
lean_dec(v___y_5219_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* lean_grind_process_new_facts(lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_){
_start:
{
lean_object* v___x_5242_; 
v___x_5242_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_, v_a_5236_, v_a_5237_, v_a_5238_, v_a_5239_, v_a_5240_);
lean_dec(v_a_5240_);
lean_dec_ref(v_a_5239_);
lean_dec(v_a_5238_);
lean_dec_ref(v_a_5237_);
lean_dec(v_a_5236_);
lean_dec_ref(v_a_5235_);
lean_dec(v_a_5234_);
lean_dec_ref(v_a_5233_);
lean_dec(v_a_5232_);
lean_dec(v_a_5231_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5256_; 
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5256_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5256_ == 0)
{
v___x_5245_ = v___x_5242_;
v_isShared_5246_ = v_isSharedCheck_5256_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5242_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5256_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v_fst_5247_; 
v_fst_5247_ = lean_ctor_get(v_a_5243_, 0);
lean_inc(v_fst_5247_);
lean_dec(v_a_5243_);
if (lean_obj_tag(v_fst_5247_) == 0)
{
lean_object* v___x_5248_; lean_object* v___x_5250_; 
v___x_5248_ = lean_box(0);
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 0, v___x_5248_);
v___x_5250_ = v___x_5245_;
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
else
{
lean_object* v_val_5252_; lean_object* v___x_5254_; 
v_val_5252_ = lean_ctor_get(v_fst_5247_, 0);
lean_inc(v_val_5252_);
lean_dec_ref_known(v_fst_5247_, 1);
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 0, v_val_5252_);
v___x_5254_ = v___x_5245_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_val_5252_);
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
else
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5264_; 
v_a_5257_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5259_ = v___x_5242_;
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5242_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5262_; 
if (v_isShared_5260_ == 0)
{
v___x_5262_ = v___x_5259_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5257_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl___boxed(lean_object* v_a_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_, lean_object* v_a_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = lean_grind_process_new_facts(v_a_5265_, v_a_5266_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(lean_object* v_inst_5277_, lean_object* v_a_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_){
_start:
{
lean_object* v___x_5290_; 
v___x_5290_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
return v___x_5290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___boxed(lean_object* v_inst_5291_, lean_object* v_a_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_){
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0(v_inst_5291_, v_a_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
lean_dec(v___y_5302_);
lean_dec_ref(v___y_5301_);
lean_dec(v___y_5300_);
lean_dec_ref(v___y_5299_);
lean_dec(v___y_5298_);
lean_dec_ref(v___y_5297_);
lean_dec(v___y_5296_);
lean_dec_ref(v___y_5295_);
lean_dec(v___y_5294_);
lean_dec(v___y_5293_);
lean_dec_ref(v_a_5292_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add(lean_object* v_fact_5305_, lean_object* v_proof_5306_, lean_object* v_generation_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_){
_start:
{
uint8_t v___x_5319_; 
lean_inc_ref(v_fact_5305_);
v___x_5319_ = l_Lean_Expr_isTrue(v_fact_5305_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; 
v___x_5320_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_5308_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5332_; 
v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5323_ = v___x_5320_;
v_isShared_5324_ = v_isSharedCheck_5332_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5320_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5332_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
uint8_t v___x_5325_; 
v___x_5325_ = lean_unbox(v_a_5321_);
lean_dec(v_a_5321_);
if (v___x_5325_ == 0)
{
lean_object* v___x_5326_; lean_object* v___x_5327_; 
lean_del_object(v___x_5323_);
v___x_5326_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_5308_);
lean_dec_ref(v___x_5326_);
v___x_5327_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(v_fact_5305_, v_proof_5306_, v_generation_5307_, v_a_5308_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_);
return v___x_5327_;
}
else
{
lean_object* v___x_5328_; lean_object* v___x_5330_; 
lean_dec(v_generation_5307_);
lean_dec_ref(v_proof_5306_);
lean_dec_ref(v_fact_5305_);
v___x_5328_ = lean_box(0);
if (v_isShared_5324_ == 0)
{
lean_ctor_set(v___x_5323_, 0, v___x_5328_);
v___x_5330_ = v___x_5323_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5328_);
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
lean_object* v_a_5333_; lean_object* v___x_5335_; uint8_t v_isShared_5336_; uint8_t v_isSharedCheck_5340_; 
lean_dec(v_generation_5307_);
lean_dec_ref(v_proof_5306_);
lean_dec_ref(v_fact_5305_);
v_a_5333_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5340_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5340_ == 0)
{
v___x_5335_ = v___x_5320_;
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
else
{
lean_inc(v_a_5333_);
lean_dec(v___x_5320_);
v___x_5335_ = lean_box(0);
v_isShared_5336_ = v_isSharedCheck_5340_;
goto v_resetjp_5334_;
}
v_resetjp_5334_:
{
lean_object* v___x_5338_; 
if (v_isShared_5336_ == 0)
{
v___x_5338_ = v___x_5335_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5339_; 
v_reuseFailAlloc_5339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5339_, 0, v_a_5333_);
v___x_5338_ = v_reuseFailAlloc_5339_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
return v___x_5338_;
}
}
}
}
else
{
lean_object* v___x_5341_; lean_object* v___x_5342_; 
lean_dec(v_generation_5307_);
lean_dec_ref(v_proof_5306_);
lean_dec_ref(v_fact_5305_);
v___x_5341_ = lean_box(0);
v___x_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5342_, 0, v___x_5341_);
return v___x_5342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_add___boxed(lean_object* v_fact_5343_, lean_object* v_proof_5344_, lean_object* v_generation_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_, lean_object* v_a_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_){
_start:
{
lean_object* v_res_5357_; 
v_res_5357_ = l_Lean_Meta_Grind_add(v_fact_5343_, v_proof_5344_, v_generation_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_, v_a_5350_, v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_);
lean_dec(v_a_5355_);
lean_dec_ref(v_a_5354_);
lean_dec(v_a_5353_);
lean_dec_ref(v_a_5352_);
lean_dec(v_a_5351_);
lean_dec_ref(v_a_5350_);
lean_dec(v_a_5349_);
lean_dec_ref(v_a_5348_);
lean_dec(v_a_5347_);
lean_dec(v_a_5346_);
return v_res_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object* v_fvarId_5358_, lean_object* v_generation_5359_, lean_object* v_a_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_, lean_object* v_a_5369_){
_start:
{
lean_object* v___x_5371_; 
lean_inc(v_fvarId_5358_);
v___x_5371_ = l_Lean_FVarId_getType___redArg(v_fvarId_5358_, v_a_5366_, v_a_5368_, v_a_5369_);
if (lean_obj_tag(v___x_5371_) == 0)
{
lean_object* v_a_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; 
v_a_5372_ = lean_ctor_get(v___x_5371_, 0);
lean_inc(v_a_5372_);
lean_dec_ref_known(v___x_5371_, 1);
v___x_5373_ = l_Lean_mkFVar(v_fvarId_5358_);
v___x_5374_ = l_Lean_Meta_Grind_add(v_a_5372_, v___x_5373_, v_generation_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_, v_a_5369_);
return v___x_5374_;
}
else
{
lean_object* v_a_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5382_; 
lean_dec(v_generation_5359_);
lean_dec(v_fvarId_5358_);
v_a_5375_ = lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5382_ == 0)
{
v___x_5377_ = v___x_5371_;
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_a_5375_);
lean_dec(v___x_5371_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5380_; 
if (v_isShared_5378_ == 0)
{
v___x_5380_ = v___x_5377_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v_a_5375_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addHypothesis___boxed(lean_object* v_fvarId_5383_, lean_object* v_generation_5384_, lean_object* v_a_5385_, lean_object* v_a_5386_, lean_object* v_a_5387_, lean_object* v_a_5388_, lean_object* v_a_5389_, lean_object* v_a_5390_, lean_object* v_a_5391_, lean_object* v_a_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l_Lean_Meta_Grind_addHypothesis(v_fvarId_5383_, v_generation_5384_, v_a_5385_, v_a_5386_, v_a_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_, v_a_5392_, v_a_5393_, v_a_5394_);
lean_dec(v_a_5394_);
lean_dec_ref(v_a_5393_);
lean_dec(v_a_5392_);
lean_dec_ref(v_a_5391_);
lean_dec(v_a_5390_);
lean_dec_ref(v_a_5389_);
lean_dec(v_a_5388_);
lean_dec_ref(v_a_5387_);
lean_dec(v_a_5386_);
lean_dec(v_a_5385_);
return v_res_5396_;
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
