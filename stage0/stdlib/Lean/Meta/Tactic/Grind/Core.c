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
size_t v_x_22424__boxed_351_; lean_object* v_res_352_; 
v_x_22424__boxed_351_ = lean_unbox_usize(v_x_349_);
lean_dec(v_x_349_);
v_res_352_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0___redArg(v___x_347_, v_x_348_, v_x_22424__boxed_351_, v_x_350_);
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
size_t v_x_22886__boxed_603_; lean_object* v_res_604_; 
v_x_22886__boxed_603_ = lean_unbox_usize(v_x_601_);
lean_dec(v_x_601_);
v_res_604_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__0_spec__0(v___x_598_, v_00_u03b2_599_, v_x_600_, v_x_22886__boxed_603_, v_x_602_);
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
return v___x_750_;
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
size_t v_x_9678__boxed_783_; uint8_t v_res_784_; lean_object* v_r_785_; 
v_x_9678__boxed_783_ = lean_unbox_usize(v_x_781_);
lean_dec(v_x_781_);
v_res_784_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1___redArg(v_x_780_, v_x_9678__boxed_783_, v_x_782_);
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
size_t v_x_9961__boxed_951_; uint8_t v_res_952_; lean_object* v_r_953_; 
v_x_9961__boxed_951_ = lean_unbox_usize(v_x_949_);
lean_dec(v_x_949_);
v_res_952_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse_spec__0_spec__0_spec__1(v_00_u03b2_947_, v_x_948_, v_x_9961__boxed_951_, v_x_950_);
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
lean_object* v_binderType_1993_; size_t v___x_1994_; size_t v___x_1995_; uint8_t v___x_1996_; 
v_binderType_1993_ = lean_ctor_get(v_a_1992_, 1);
v___x_1994_ = lean_ptr_addr(v_d_1979_);
v___x_1995_ = lean_ptr_addr(v_binderType_1993_);
v___x_1996_ = lean_usize_dec_eq(v___x_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
v_a_1985_ = v___x_1991_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_inc_ref(v_a_1992_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_a_1992_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
lean_ctor_set(v___x_1999_, 1, v___x_1990_);
return v___x_1999_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___boxed(lean_object* v_d_2000_, lean_object* v_as_2001_, lean_object* v_sz_2002_, lean_object* v_i_2003_, lean_object* v_b_2004_){
_start:
{
size_t v_sz_boxed_2005_; size_t v_i_boxed_2006_; lean_object* v_res_2007_; 
v_sz_boxed_2005_ = lean_unbox_usize(v_sz_2002_);
lean_dec(v_sz_2002_);
v_i_boxed_2006_ = lean_unbox_usize(v_i_2003_);
lean_dec(v_i_2003_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2000_, v_as_2001_, v_sz_boxed_2005_, v_i_boxed_2006_, v_b_2004_);
lean_dec_ref(v_b_2004_);
lean_dec_ref(v_as_2001_);
lean_dec_ref(v_d_2000_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(lean_object* v_lams_2008_, lean_object* v_d_2009_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; size_t v_sz_2012_; size_t v___x_2013_; lean_object* v___x_2014_; lean_object* v_fst_2015_; 
v___x_2010_ = lean_box(0);
v___x_2011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0___closed__0));
v_sz_2012_ = lean_array_size(v_lams_2008_);
v___x_2013_ = ((size_t)0ULL);
v___x_2014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f_spec__0(v_d_2009_, v_lams_2008_, v_sz_2012_, v___x_2013_, v___x_2011_);
v_fst_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_fst_2015_);
lean_dec_ref(v___x_2014_);
if (lean_obj_tag(v_fst_2015_) == 0)
{
return v___x_2010_;
}
else
{
lean_object* v_val_2016_; 
v_val_2016_ = lean_ctor_get(v_fst_2015_, 0);
lean_inc(v_val_2016_);
lean_dec_ref_known(v_fst_2015_, 1);
return v_val_2016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f___boxed(lean_object* v_lams_2017_, lean_object* v_d_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_2017_, v_d_2018_);
lean_dec_ref(v_d_2018_);
lean_dec_ref(v_lams_2017_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(lean_object* v_lams_u2082_2030_, lean_object* v_lams_u2081_2031_, lean_object* v_as_2032_, size_t v_sz_2033_, size_t v_i_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_a_2048_; uint8_t v___x_2052_; 
v___x_2052_ = lean_usize_dec_lt(v_i_2034_, v_sz_2033_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v_b_2035_);
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v_a_2055_; 
v___x_2054_ = lean_box(0);
v_a_2055_ = lean_array_uget_borrowed(v_as_2032_, v_i_2034_);
if (lean_obj_tag(v_a_2055_) == 6)
{
lean_object* v_binderType_2056_; lean_object* v_body_2057_; lean_object* v___x_2058_; 
v_binderType_2056_ = lean_ctor_get(v_a_2055_, 1);
v_body_2057_ = lean_ctor_get(v_a_2055_, 2);
lean_inc_ref(v_binderType_2056_);
v___x_2058_ = l_Lean_Meta_getLevel(v_binderType_2056_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__1));
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2062_, 0, v_a_2059_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
lean_inc_ref(v___x_2062_);
v___x_2063_ = l_Lean_mkConst(v___x_2060_, v___x_2062_);
lean_inc_ref(v_binderType_2056_);
v___x_2064_ = l_Lean_Expr_app___override(v___x_2063_, v_binderType_2056_);
v___x_2065_ = lean_box(0);
v___x_2066_ = l_Lean_Meta_synthInstance_x3f(v___x_2064_, v___x_2065_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
if (lean_obj_tag(v_a_2067_) == 1)
{
lean_object* v_val_2068_; lean_object* v___x_2069_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; uint8_t v___x_2134_; 
v_val_2068_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_val_2068_);
lean_dec_ref_known(v_a_2067_, 1);
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2134_ = l_Lean_Expr_hasLooseBVars(v_body_2057_);
if (v___x_2134_ == 0)
{
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
goto v___jp_2070_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__5));
lean_inc_ref(v___x_2062_);
v___x_2136_ = l_Lean_mkConst(v___x_2135_, v___x_2062_);
lean_inc_ref(v_binderType_2056_);
v___x_2137_ = l_Lean_Expr_app___override(v___x_2136_, v_binderType_2056_);
v___x_2138_ = l_Lean_Meta_synthInstance_x3f(v___x_2137_, v___x_2065_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
if (lean_obj_tag(v_a_2139_) == 0)
{
lean_dec(v_val_2068_);
lean_dec_ref_known(v___x_2062_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
else
{
lean_dec_ref_known(v_a_2139_, 1);
if (v___x_2134_ == 0)
{
lean_dec(v_val_2068_);
lean_dec_ref_known(v___x_2062_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
else
{
v___y_2071_ = v___y_2036_;
v___y_2072_ = v___y_2037_;
v___y_2073_ = v___y_2038_;
v___y_2074_ = v___y_2039_;
v___y_2075_ = v___y_2040_;
v___y_2076_ = v___y_2041_;
v___y_2077_ = v___y_2042_;
v___y_2078_ = v___y_2043_;
v___y_2079_ = v___y_2044_;
v___y_2080_ = v___y_2045_;
goto v___jp_2070_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_val_2068_);
lean_dec_ref_known(v___x_2062_, 2);
v_a_2140_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2138_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2138_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
v___jp_2070_:
{
lean_object* v___x_2081_; 
v___x_2081_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_getFunWithGivenDomain_x3f(v_lams_u2082_2030_, v_binderType_2056_);
if (lean_obj_tag(v___x_2081_) == 1)
{
lean_object* v_val_2082_; 
v_val_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_val_2082_);
lean_dec_ref_known(v___x_2081_, 1);
if (lean_obj_tag(v_val_2082_) == 6)
{
lean_object* v_binderType_2083_; lean_object* v_body_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_binderType_2083_ = lean_ctor_get(v_val_2082_, 1);
lean_inc_ref(v_binderType_2083_);
v_body_2084_ = lean_ctor_get(v_val_2082_, 2);
lean_inc_ref(v_body_2084_);
lean_dec_ref_known(v_val_2082_, 3);
v___x_2085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___closed__3));
v___x_2086_ = l_Lean_mkConst(v___x_2085_, v___x_2062_);
v___x_2087_ = l_Lean_mkAppB(v___x_2086_, v_binderType_2083_, v_val_2068_);
v___x_2088_ = l_Lean_Meta_Grind_preprocessLight___redArg(v___x_2087_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2090_ = lean_array_fget_borrowed(v_lams_u2081_2031_, v___x_2069_);
v___x_2091_ = lean_array_fget_borrowed(v_lams_u2082_2030_, v___x_2069_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
lean_inc(v___y_2076_);
lean_inc_ref(v___y_2075_);
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
lean_inc(v___y_2072_);
lean_inc(v___y_2071_);
lean_inc(v___x_2091_);
lean_inc(v___x_2090_);
v___x_2092_ = lean_grind_mk_eq_proof(v___x_2090_, v___x_2091_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = lean_expr_instantiate1(v_body_2057_, v_a_2089_);
v___x_2095_ = lean_expr_instantiate1(v_body_2084_, v_a_2089_);
lean_dec_ref(v_body_2084_);
v___x_2096_ = l_Lean_Meta_mkCongrFun(v_a_2093_, v_a_2089_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = l_Lean_Meta_mkEq(v___x_2094_, v___x_2095_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v___x_2100_ = l_Lean_Meta_mkExpectedPropHint(v_a_2097_, v_a_2099_);
v___x_2101_ = l_Lean_Meta_Grind_pushNewFact(v___x_2100_, v___x_2069_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_dec_ref_known(v___x_2101_, 1);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
else
{
return v___x_2101_;
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_a_2097_);
v_a_2102_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2098_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2098_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v___x_2095_);
lean_dec_ref(v___x_2094_);
v_a_2110_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2096_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2096_);
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
lean_dec(v_a_2089_);
lean_dec_ref(v_body_2084_);
v_a_2118_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2092_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2092_);
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
lean_dec_ref(v_body_2084_);
v_a_2126_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2088_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2088_);
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
lean_dec(v_val_2082_);
lean_dec(v_val_2068_);
lean_dec_ref_known(v___x_2062_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
else
{
lean_dec(v___x_2081_);
lean_dec(v_val_2068_);
lean_dec_ref_known(v___x_2062_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
}
else
{
lean_dec(v_a_2067_);
lean_dec_ref_known(v___x_2062_, 2);
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref_known(v___x_2062_, 2);
v_a_2148_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2066_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2066_);
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
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
v_a_2156_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2058_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2058_);
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
v_a_2048_ = v___x_2054_;
goto v___jp_2047_;
}
}
v___jp_2047_:
{
size_t v___x_2049_; size_t v___x_2050_; 
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_add(v_i_2034_, v___x_2049_);
v_i_2034_ = v___x_2050_;
v_b_2035_ = v_a_2048_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0___boxed(lean_object** _args){
lean_object* v_lams_u2082_2164_ = _args[0];
lean_object* v_lams_u2081_2165_ = _args[1];
lean_object* v_as_2166_ = _args[2];
lean_object* v_sz_2167_ = _args[3];
lean_object* v_i_2168_ = _args[4];
lean_object* v_b_2169_ = _args[5];
lean_object* v___y_2170_ = _args[6];
lean_object* v___y_2171_ = _args[7];
lean_object* v___y_2172_ = _args[8];
lean_object* v___y_2173_ = _args[9];
lean_object* v___y_2174_ = _args[10];
lean_object* v___y_2175_ = _args[11];
lean_object* v___y_2176_ = _args[12];
lean_object* v___y_2177_ = _args[13];
lean_object* v___y_2178_ = _args[14];
lean_object* v___y_2179_ = _args[15];
lean_object* v___y_2180_ = _args[16];
_start:
{
size_t v_sz_boxed_2181_; size_t v_i_boxed_2182_; lean_object* v_res_2183_; 
v_sz_boxed_2181_ = lean_unbox_usize(v_sz_2167_);
lean_dec(v_sz_2167_);
v_i_boxed_2182_ = lean_unbox_usize(v_i_2168_);
lean_dec(v_i_2168_);
v_res_2183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2164_, v_lams_u2081_2165_, v_as_2166_, v_sz_boxed_2181_, v_i_boxed_2182_, v_b_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v_as_2166_);
lean_dec_ref(v_lams_u2081_2165_);
lean_dec_ref(v_lams_u2082_2164_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(lean_object* v_lams_u2081_2184_, lean_object* v_lams_u2082_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v___x_2197_ = lean_array_get_size(v_lams_u2081_2184_);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = lean_nat_dec_eq(v___x_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = lean_array_get_size(v_lams_u2082_2185_);
v___x_2201_ = lean_nat_dec_eq(v___x_2200_, v___x_2198_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; size_t v_sz_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2202_ = lean_box(0);
v_sz_2203_ = lean_array_size(v_lams_u2081_2184_);
v___x_2204_ = ((size_t)0ULL);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns_spec__0(v_lams_u2082_2185_, v_lams_u2081_2184_, v_lams_u2081_2184_, v_sz_2203_, v___x_2204_, v___x_2202_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v___x_2205_, 0);
lean_dec(v_unused_2213_);
v___x_2207_ = v___x_2205_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v___x_2205_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2202_);
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2202_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
return v___x_2205_;
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
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_box(0);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns___boxed(lean_object* v_lams_u2081_2218_, lean_object* v_lams_u2082_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v_lams_u2081_2218_, v_lams_u2082_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_lams_u2082_2219_);
lean_dec_ref(v_lams_u2081_2218_);
return v_res_2231_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(lean_object* v_x_2232_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg___boxed(lean_object* v_x_2234_){
_start:
{
uint8_t v_res_2235_; lean_object* v_r_2236_; 
v_res_2235_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___redArg(v_x_2234_);
lean_dec_ref(v_x_2234_);
v_r_2236_ = lean_box(v_res_2235_);
return v_r_2236_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(lean_object* v_00_u03b2_2237_, lean_object* v_x_2238_){
_start:
{
uint8_t v___x_2239_; 
v___x_2239_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0___boxed(lean_object* v_00_u03b2_2240_, lean_object* v_x_2241_){
_start:
{
uint8_t v_res_2242_; lean_object* v_r_2243_; 
v_res_2242_ = l_Lean_PersistentHashMap_isEmpty___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__0(v_00_u03b2_2240_, v_x_2241_);
lean_dec_ref(v_x_2241_);
v_r_2243_ = lean_box(v_res_2242_);
return v_r_2243_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(lean_object* v_xs_2244_, lean_object* v_v_2245_, lean_object* v_i_2246_){
_start:
{
lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2247_ = lean_array_get_size(v_xs_2244_);
v___x_2248_ = lean_nat_dec_lt(v_i_2246_, v___x_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; 
lean_dec(v_i_2246_);
v___x_2249_ = lean_box(0);
return v___x_2249_;
}
else
{
lean_object* v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; uint8_t v___x_2253_; 
v___x_2250_ = lean_array_fget_borrowed(v_xs_2244_, v_i_2246_);
v___x_2251_ = lean_ptr_addr(v___x_2250_);
v___x_2252_ = lean_ptr_addr(v_v_2245_);
v___x_2253_ = lean_usize_dec_eq(v___x_2251_, v___x_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_unsigned_to_nat(1u);
v___x_2255_ = lean_nat_add(v_i_2246_, v___x_2254_);
lean_dec(v_i_2246_);
v_i_2246_ = v___x_2255_;
goto _start;
}
else
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v_i_2246_);
return v___x_2257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_xs_2258_, lean_object* v_v_2259_, lean_object* v_i_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2258_, v_v_2259_, v_i_2260_);
lean_dec_ref(v_v_2259_);
lean_dec_ref(v_xs_2258_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(lean_object* v_xs_2262_, lean_object* v_v_2263_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_unsigned_to_nat(0u);
v___x_2265_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5_spec__8(v_xs_2262_, v_v_2263_, v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5___boxed(lean_object* v_xs_2266_, lean_object* v_v_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_xs_2266_, v_v_2267_);
lean_dec_ref(v_v_2267_);
lean_dec_ref(v_xs_2266_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(lean_object* v_x_2269_, size_t v_x_2270_, lean_object* v_x_2271_){
_start:
{
if (lean_obj_tag(v_x_2269_) == 0)
{
lean_object* v_es_2272_; lean_object* v___x_2273_; size_t v___x_2274_; size_t v___x_2275_; lean_object* v_j_2276_; lean_object* v_entry_2277_; 
v_es_2272_ = lean_ctor_get(v_x_2269_, 0);
v___x_2273_ = lean_box(2);
v___x_2274_ = ((size_t)31ULL);
v___x_2275_ = lean_usize_land(v_x_2270_, v___x_2274_);
v_j_2276_ = lean_usize_to_nat(v___x_2275_);
v_entry_2277_ = lean_array_get(v___x_2273_, v_es_2272_, v_j_2276_);
switch(lean_obj_tag(v_entry_2277_))
{
case 0:
{
lean_object* v_key_2278_; size_t v___x_2279_; size_t v___x_2280_; uint8_t v___x_2281_; 
v_key_2278_ = lean_ctor_get(v_entry_2277_, 0);
lean_inc(v_key_2278_);
lean_dec_ref_known(v_entry_2277_, 2);
v___x_2279_ = lean_ptr_addr(v_x_2271_);
v___x_2280_ = lean_ptr_addr(v_key_2278_);
lean_dec(v_key_2278_);
v___x_2281_ = lean_usize_dec_eq(v___x_2279_, v___x_2280_);
if (v___x_2281_ == 0)
{
lean_dec(v_j_2276_);
return v_x_2269_;
}
else
{
lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2289_; 
lean_inc_ref(v_es_2272_);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_x_2269_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; 
v_unused_2290_ = lean_ctor_get(v_x_2269_, 0);
lean_dec(v_unused_2290_);
v___x_2283_ = v_x_2269_;
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
else
{
lean_dec(v_x_2269_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_array_set(v_es_2272_, v_j_2276_, v___x_2273_);
lean_dec(v_j_2276_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2285_);
v___x_2287_ = v___x_2283_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
case 1:
{
lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2325_; 
lean_inc_ref(v_es_2272_);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_x_2269_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v_x_2269_, 0);
lean_dec(v_unused_2326_);
v___x_2292_ = v_x_2269_;
v_isShared_2293_ = v_isSharedCheck_2325_;
goto v_resetjp_2291_;
}
else
{
lean_dec(v_x_2269_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2325_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_node_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2324_; 
v_node_2294_ = lean_ctor_get(v_entry_2277_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_entry_2277_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2296_ = v_entry_2277_;
v_isShared_2297_ = v_isSharedCheck_2324_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_node_2294_);
lean_dec(v_entry_2277_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2324_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
size_t v___x_2298_; lean_object* v_entries_2299_; size_t v___x_2300_; lean_object* v_newNode_2301_; lean_object* v___x_2302_; 
v___x_2298_ = ((size_t)5ULL);
v_entries_2299_ = lean_array_set(v_es_2272_, v_j_2276_, v___x_2273_);
v___x_2300_ = lean_usize_shift_right(v_x_2270_, v___x_2298_);
v_newNode_2301_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_node_2294_, v___x_2300_, v_x_2271_);
lean_inc_ref(v_newNode_2301_);
v___x_2302_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2304_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_newNode_2301_);
v___x_2304_ = v___x_2296_;
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
v___x_2305_ = lean_array_set(v_entries_2299_, v_j_2276_, v___x_2304_);
lean_dec(v_j_2276_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2305_);
v___x_2307_ = v___x_2292_;
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
lean_del_object(v___x_2296_);
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
v___x_2318_ = lean_array_set(v_entries_2299_, v_j_2276_, v___x_2317_);
lean_dec(v_j_2276_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2318_);
v___x_2320_ = v___x_2292_;
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
lean_dec(v_j_2276_);
return v_x_2269_;
}
}
}
else
{
lean_object* v_ks_2327_; lean_object* v_vs_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2342_; 
v_ks_2327_ = lean_ctor_get(v_x_2269_, 0);
v_vs_2328_ = lean_ctor_get(v_x_2269_, 1);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_x_2269_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2330_ = v_x_2269_;
v_isShared_2331_ = v_isSharedCheck_2342_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_vs_2328_);
lean_inc(v_ks_2327_);
lean_dec(v_x_2269_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2342_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3_spec__5(v_ks_2327_, v_x_2271_);
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
size_t v_x_19384__boxed_2346_; lean_object* v_res_2347_; 
v_x_19384__boxed_2346_ = lean_unbox_usize(v_x_2344_);
lean_dec(v_x_2344_);
v_res_2347_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2343_, v_x_19384__boxed_2346_, v_x_2345_);
lean_dec_ref(v_x_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
size_t v___x_2350_; size_t v___x_2351_; size_t v___x_2352_; uint64_t v___x_2353_; size_t v_h_2354_; lean_object* v___x_2355_; 
v___x_2350_ = lean_ptr_addr(v_x_2349_);
v___x_2351_ = ((size_t)3ULL);
v___x_2352_ = lean_usize_shift_right(v___x_2350_, v___x_2351_);
v___x_2353_ = lean_usize_to_uint64(v___x_2352_);
v_h_2354_ = lean_uint64_to_usize(v___x_2353_);
v___x_2355_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2348_, v_h_2354_, v_x_2349_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg___boxed(lean_object* v_x_2356_, lean_object* v_x_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2356_, v_x_2357_);
lean_dec_ref(v_x_2357_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(lean_object* v_as_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
if (lean_obj_tag(v_as_2359_) == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_box(0);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
else
{
lean_object* v_head_2373_; lean_object* v_tail_2374_; lean_object* v___x_2375_; 
v_head_2373_ = lean_ctor_get(v_as_2359_, 0);
lean_inc(v_head_2373_);
v_tail_2374_ = lean_ctor_get(v_as_2359_, 1);
lean_inc(v_tail_2374_);
lean_dec_ref_known(v_as_2359_, 2);
v___x_2375_ = l_Lean_Meta_Grind_DelayedTheoremInstance_check(v_head_2373_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_dec_ref_known(v___x_2375_, 1);
v_as_2359_ = v_tail_2374_;
goto _start;
}
else
{
lean_dec(v_tail_2374_);
return v___x_2375_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3___boxed(lean_object* v_as_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_as_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec(v___y_2378_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_2390_, lean_object* v_vals_2391_, lean_object* v_i_2392_, lean_object* v_k_2393_){
_start:
{
lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2394_ = lean_array_get_size(v_keys_2390_);
v___x_2395_ = lean_nat_dec_lt(v_i_2392_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
lean_dec(v_i_2392_);
v___x_2396_ = lean_box(0);
return v___x_2396_;
}
else
{
lean_object* v_k_x27_2397_; size_t v___x_2398_; size_t v___x_2399_; uint8_t v___x_2400_; 
v_k_x27_2397_ = lean_array_fget_borrowed(v_keys_2390_, v_i_2392_);
v___x_2398_ = lean_ptr_addr(v_k_2393_);
v___x_2399_ = lean_ptr_addr(v_k_x27_2397_);
v___x_2400_ = lean_usize_dec_eq(v___x_2398_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = lean_unsigned_to_nat(1u);
v___x_2402_ = lean_nat_add(v_i_2392_, v___x_2401_);
lean_dec(v_i_2392_);
v_i_2392_ = v___x_2402_;
goto _start;
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_array_fget_borrowed(v_vals_2391_, v_i_2392_);
lean_dec(v_i_2392_);
lean_inc(v___x_2404_);
v___x_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_2406_, lean_object* v_vals_2407_, lean_object* v_i_2408_, lean_object* v_k_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2406_, v_vals_2407_, v_i_2408_, v_k_2409_);
lean_dec_ref(v_k_2409_);
lean_dec_ref(v_vals_2407_);
lean_dec_ref(v_keys_2406_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(lean_object* v_x_2411_, size_t v_x_2412_, lean_object* v_x_2413_){
_start:
{
if (lean_obj_tag(v_x_2411_) == 0)
{
lean_object* v_es_2414_; lean_object* v___x_2415_; size_t v___x_2416_; size_t v___x_2417_; lean_object* v_j_2418_; lean_object* v___x_2419_; 
v_es_2414_ = lean_ctor_get(v_x_2411_, 0);
v___x_2415_ = lean_box(2);
v___x_2416_ = ((size_t)31ULL);
v___x_2417_ = lean_usize_land(v_x_2412_, v___x_2416_);
v_j_2418_ = lean_usize_to_nat(v___x_2417_);
v___x_2419_ = lean_array_get_borrowed(v___x_2415_, v_es_2414_, v_j_2418_);
lean_dec(v_j_2418_);
switch(lean_obj_tag(v___x_2419_))
{
case 0:
{
lean_object* v_key_2420_; lean_object* v_val_2421_; size_t v___x_2422_; size_t v___x_2423_; uint8_t v___x_2424_; 
v_key_2420_ = lean_ctor_get(v___x_2419_, 0);
v_val_2421_ = lean_ctor_get(v___x_2419_, 1);
v___x_2422_ = lean_ptr_addr(v_x_2413_);
v___x_2423_ = lean_ptr_addr(v_key_2420_);
v___x_2424_ = lean_usize_dec_eq(v___x_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_box(0);
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; 
lean_inc(v_val_2421_);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_val_2421_);
return v___x_2426_;
}
}
case 1:
{
lean_object* v_node_2427_; size_t v___x_2428_; size_t v___x_2429_; 
v_node_2427_ = lean_ctor_get(v___x_2419_, 0);
v___x_2428_ = ((size_t)5ULL);
v___x_2429_ = lean_usize_shift_right(v_x_2412_, v___x_2428_);
v_x_2411_ = v_node_2427_;
v_x_2412_ = v___x_2429_;
goto _start;
}
default: 
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_box(0);
return v___x_2431_;
}
}
}
else
{
lean_object* v_ks_2432_; lean_object* v_vs_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v_ks_2432_ = lean_ctor_get(v_x_2411_, 0);
v_vs_2433_ = lean_ctor_get(v_x_2411_, 1);
v___x_2434_ = lean_unsigned_to_nat(0u);
v___x_2435_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_ks_2432_, v_vs_2433_, v___x_2434_, v_x_2413_);
return v___x_2435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg___boxed(lean_object* v_x_2436_, lean_object* v_x_2437_, lean_object* v_x_2438_){
_start:
{
size_t v_x_19609__boxed_2439_; lean_object* v_res_2440_; 
v_x_19609__boxed_2439_ = lean_unbox_usize(v_x_2437_);
lean_dec(v_x_2437_);
v_res_2440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2436_, v_x_19609__boxed_2439_, v_x_2438_);
lean_dec_ref(v_x_2438_);
lean_dec_ref(v_x_2436_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(lean_object* v_x_2441_, lean_object* v_x_2442_){
_start:
{
size_t v___x_2443_; size_t v___x_2444_; size_t v___x_2445_; uint64_t v___x_2446_; size_t v___x_2447_; lean_object* v___x_2448_; 
v___x_2443_ = lean_ptr_addr(v_x_2442_);
v___x_2444_ = ((size_t)3ULL);
v___x_2445_ = lean_usize_shift_right(v___x_2443_, v___x_2444_);
v___x_2446_ = lean_usize_to_uint64(v___x_2445_);
v___x_2447_ = lean_uint64_to_usize(v___x_2446_);
v___x_2448_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2441_, v___x_2447_, v_x_2442_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg___boxed(lean_object* v_x_2449_, lean_object* v_x_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2449_, v_x_2450_);
lean_dec_ref(v_x_2450_);
lean_dec_ref(v_x_2449_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(lean_object* v_as_x27_2452_, lean_object* v_b_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
if (lean_obj_tag(v_as_x27_2452_) == 0)
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v_b_2453_);
return v___x_2465_;
}
else
{
lean_object* v_head_2466_; lean_object* v_tail_2467_; lean_object* v___x_2468_; lean_object* v_toGoalState_2469_; lean_object* v_ematch_2470_; lean_object* v_delayedThmInsts_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_head_2466_ = lean_ctor_get(v_as_x27_2452_, 0);
v_tail_2467_ = lean_ctor_get(v_as_x27_2452_, 1);
v___x_2468_ = lean_st_ref_get(v___y_2454_);
v_toGoalState_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc_ref(v_toGoalState_2469_);
lean_dec(v___x_2468_);
v_ematch_2470_ = lean_ctor_get(v_toGoalState_2469_, 12);
lean_inc_ref(v_ematch_2470_);
lean_dec_ref(v_toGoalState_2469_);
v_delayedThmInsts_2471_ = lean_ctor_get(v_ematch_2470_, 10);
lean_inc_ref(v_delayedThmInsts_2471_);
lean_dec_ref(v_ematch_2470_);
v___x_2472_ = lean_box(0);
v___x_2473_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_delayedThmInsts_2471_, v_head_2466_);
lean_dec_ref(v_delayedThmInsts_2471_);
if (lean_obj_tag(v___x_2473_) == 1)
{
lean_object* v_val_2474_; lean_object* v___x_2475_; lean_object* v_toGoalState_2476_; lean_object* v_ematch_2477_; lean_object* v_mvarId_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2532_; 
v_val_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_val_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = lean_st_ref_take(v___y_2454_);
v_toGoalState_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc_ref(v_toGoalState_2476_);
v_ematch_2477_ = lean_ctor_get(v_toGoalState_2476_, 12);
lean_inc_ref(v_ematch_2477_);
v_mvarId_2478_ = lean_ctor_get(v___x_2475_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2475_, 0);
lean_dec(v_unused_2533_);
v___x_2480_ = v___x_2475_;
v_isShared_2481_ = v_isSharedCheck_2532_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_mvarId_2478_);
lean_dec(v___x_2475_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2532_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_nextDeclIdx_2482_; lean_object* v_enodeMap_2483_; lean_object* v_exprs_2484_; lean_object* v_parents_2485_; lean_object* v_congrTable_2486_; lean_object* v_appMap_2487_; lean_object* v_indicesFound_2488_; lean_object* v_newFacts_2489_; uint8_t v_inconsistent_2490_; lean_object* v_nextIdx_2491_; lean_object* v_newRawFacts_2492_; lean_object* v_facts_2493_; lean_object* v_extThms_2494_; lean_object* v_inj_2495_; lean_object* v_split_2496_; lean_object* v_clean_2497_; lean_object* v_sstates_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2530_; 
v_nextDeclIdx_2482_ = lean_ctor_get(v_toGoalState_2476_, 0);
v_enodeMap_2483_ = lean_ctor_get(v_toGoalState_2476_, 1);
v_exprs_2484_ = lean_ctor_get(v_toGoalState_2476_, 2);
v_parents_2485_ = lean_ctor_get(v_toGoalState_2476_, 3);
v_congrTable_2486_ = lean_ctor_get(v_toGoalState_2476_, 4);
v_appMap_2487_ = lean_ctor_get(v_toGoalState_2476_, 5);
v_indicesFound_2488_ = lean_ctor_get(v_toGoalState_2476_, 6);
v_newFacts_2489_ = lean_ctor_get(v_toGoalState_2476_, 7);
v_inconsistent_2490_ = lean_ctor_get_uint8(v_toGoalState_2476_, sizeof(void*)*17);
v_nextIdx_2491_ = lean_ctor_get(v_toGoalState_2476_, 8);
v_newRawFacts_2492_ = lean_ctor_get(v_toGoalState_2476_, 9);
v_facts_2493_ = lean_ctor_get(v_toGoalState_2476_, 10);
v_extThms_2494_ = lean_ctor_get(v_toGoalState_2476_, 11);
v_inj_2495_ = lean_ctor_get(v_toGoalState_2476_, 13);
v_split_2496_ = lean_ctor_get(v_toGoalState_2476_, 14);
v_clean_2497_ = lean_ctor_get(v_toGoalState_2476_, 15);
v_sstates_2498_ = lean_ctor_get(v_toGoalState_2476_, 16);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_toGoalState_2476_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v_toGoalState_2476_, 12);
lean_dec(v_unused_2531_);
v___x_2500_ = v_toGoalState_2476_;
v_isShared_2501_ = v_isSharedCheck_2530_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_sstates_2498_);
lean_inc(v_clean_2497_);
lean_inc(v_split_2496_);
lean_inc(v_inj_2495_);
lean_inc(v_extThms_2494_);
lean_inc(v_facts_2493_);
lean_inc(v_newRawFacts_2492_);
lean_inc(v_nextIdx_2491_);
lean_inc(v_newFacts_2489_);
lean_inc(v_indicesFound_2488_);
lean_inc(v_appMap_2487_);
lean_inc(v_congrTable_2486_);
lean_inc(v_parents_2485_);
lean_inc(v_exprs_2484_);
lean_inc(v_enodeMap_2483_);
lean_inc(v_nextDeclIdx_2482_);
lean_dec(v_toGoalState_2476_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2530_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_thmMap_2502_; lean_object* v_gmt_2503_; lean_object* v_thms_2504_; lean_object* v_newThms_2505_; lean_object* v_numInstances_2506_; lean_object* v_numDelayedInstances_2507_; lean_object* v_num_2508_; lean_object* v_preInstances_2509_; lean_object* v_nextThmIdx_2510_; lean_object* v_matchEqNames_2511_; lean_object* v_delayedThmInsts_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2529_; 
v_thmMap_2502_ = lean_ctor_get(v_ematch_2477_, 0);
v_gmt_2503_ = lean_ctor_get(v_ematch_2477_, 1);
v_thms_2504_ = lean_ctor_get(v_ematch_2477_, 2);
v_newThms_2505_ = lean_ctor_get(v_ematch_2477_, 3);
v_numInstances_2506_ = lean_ctor_get(v_ematch_2477_, 4);
v_numDelayedInstances_2507_ = lean_ctor_get(v_ematch_2477_, 5);
v_num_2508_ = lean_ctor_get(v_ematch_2477_, 6);
v_preInstances_2509_ = lean_ctor_get(v_ematch_2477_, 7);
v_nextThmIdx_2510_ = lean_ctor_get(v_ematch_2477_, 8);
v_matchEqNames_2511_ = lean_ctor_get(v_ematch_2477_, 9);
v_delayedThmInsts_2512_ = lean_ctor_get(v_ematch_2477_, 10);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_ematch_2477_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2514_ = v_ematch_2477_;
v_isShared_2515_ = v_isSharedCheck_2529_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_delayedThmInsts_2512_);
lean_inc(v_matchEqNames_2511_);
lean_inc(v_nextThmIdx_2510_);
lean_inc(v_preInstances_2509_);
lean_inc(v_num_2508_);
lean_inc(v_numDelayedInstances_2507_);
lean_inc(v_numInstances_2506_);
lean_inc(v_newThms_2505_);
lean_inc(v_thms_2504_);
lean_inc(v_gmt_2503_);
lean_inc(v_thmMap_2502_);
lean_dec(v_ematch_2477_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2529_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_delayedThmInsts_2512_, v_head_2466_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 10, v___x_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_thmMap_2502_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_gmt_2503_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_thms_2504_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v_newThms_2505_);
lean_ctor_set(v_reuseFailAlloc_2528_, 4, v_numInstances_2506_);
lean_ctor_set(v_reuseFailAlloc_2528_, 5, v_numDelayedInstances_2507_);
lean_ctor_set(v_reuseFailAlloc_2528_, 6, v_num_2508_);
lean_ctor_set(v_reuseFailAlloc_2528_, 7, v_preInstances_2509_);
lean_ctor_set(v_reuseFailAlloc_2528_, 8, v_nextThmIdx_2510_);
lean_ctor_set(v_reuseFailAlloc_2528_, 9, v_matchEqNames_2511_);
lean_ctor_set(v_reuseFailAlloc_2528_, 10, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 12, v___x_2518_);
v___x_2520_ = v___x_2500_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_nextDeclIdx_2482_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_enodeMap_2483_);
lean_ctor_set(v_reuseFailAlloc_2527_, 2, v_exprs_2484_);
lean_ctor_set(v_reuseFailAlloc_2527_, 3, v_parents_2485_);
lean_ctor_set(v_reuseFailAlloc_2527_, 4, v_congrTable_2486_);
lean_ctor_set(v_reuseFailAlloc_2527_, 5, v_appMap_2487_);
lean_ctor_set(v_reuseFailAlloc_2527_, 6, v_indicesFound_2488_);
lean_ctor_set(v_reuseFailAlloc_2527_, 7, v_newFacts_2489_);
lean_ctor_set(v_reuseFailAlloc_2527_, 8, v_nextIdx_2491_);
lean_ctor_set(v_reuseFailAlloc_2527_, 9, v_newRawFacts_2492_);
lean_ctor_set(v_reuseFailAlloc_2527_, 10, v_facts_2493_);
lean_ctor_set(v_reuseFailAlloc_2527_, 11, v_extThms_2494_);
lean_ctor_set(v_reuseFailAlloc_2527_, 12, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2527_, 13, v_inj_2495_);
lean_ctor_set(v_reuseFailAlloc_2527_, 14, v_split_2496_);
lean_ctor_set(v_reuseFailAlloc_2527_, 15, v_clean_2497_);
lean_ctor_set(v_reuseFailAlloc_2527_, 16, v_sstates_2498_);
lean_ctor_set_uint8(v_reuseFailAlloc_2527_, sizeof(void*)*17, v_inconsistent_2490_);
v___x_2520_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2522_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2520_);
v___x_2522_ = v___x_2480_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_mvarId_2478_);
v___x_2522_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_st_ref_put(v___y_2454_, v___x_2522_);
v___x_2524_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__3(v_val_2474_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_dec_ref_known(v___x_2524_, 1);
v_as_x27_2452_ = v_tail_2467_;
v_b_2453_ = v___x_2472_;
goto _start;
}
else
{
return v___x_2524_;
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
lean_dec(v___x_2473_);
v_as_x27_2452_ = v_tail_2467_;
v_b_2453_ = v___x_2472_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg___boxed(lean_object* v_as_x27_2535_, lean_object* v_b_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2535_, v_b_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec(v_as_x27_2535_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(lean_object* v_toPropagateDown_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_2550_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2590_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2590_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2590_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
uint8_t v___x_2566_; 
v___x_2566_ = lean_unbox(v_a_2562_);
lean_dec(v_a_2562_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v_toGoalState_2568_; lean_object* v_ematch_2569_; lean_object* v_delayedThmInsts_2570_; uint8_t v___x_2571_; 
v___x_2567_ = lean_st_ref_get(v_a_2550_);
v_toGoalState_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_ref(v_toGoalState_2568_);
lean_dec(v___x_2567_);
v_ematch_2569_ = lean_ctor_get(v_toGoalState_2568_, 12);
lean_inc_ref(v_ematch_2569_);
lean_dec_ref(v_toGoalState_2568_);
v_delayedThmInsts_2570_ = lean_ctor_get(v_ematch_2569_, 10);
lean_inc_ref(v_delayedThmInsts_2570_);
lean_dec_ref(v_ematch_2569_);
v___x_2571_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_delayedThmInsts_2570_);
lean_dec_ref(v_delayedThmInsts_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_del_object(v___x_2564_);
v___x_2572_ = lean_box(0);
v___x_2573_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_toPropagateDown_2549_, v___x_2572_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; 
v_unused_2581_ = lean_ctor_get(v___x_2573_, 0);
lean_dec(v_unused_2581_);
v___x_2575_ = v___x_2573_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_dec(v___x_2573_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2572_);
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2572_);
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
return v___x_2573_;
}
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2582_ = lean_box(0);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2582_);
v___x_2584_ = v___x_2564_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = lean_box(0);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v___x_2586_);
v___x_2588_ = v___x_2564_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
v_a_2591_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2561_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2561_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts___boxed(lean_object* v_toPropagateDown_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v_toPropagateDown_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec(v_toPropagateDown_2599_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(lean_object* v_00_u03b2_2612_, lean_object* v_x_2613_, lean_object* v_x_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___redArg(v_x_2613_, v_x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1___boxed(lean_object* v_00_u03b2_2616_, lean_object* v_x_2617_, lean_object* v_x_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1(v_00_u03b2_2616_, v_x_2617_, v_x_2618_);
lean_dec_ref(v_x_2618_);
lean_dec_ref(v_x_2617_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(lean_object* v_00_u03b2_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___redArg(v_x_2621_, v_x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2___boxed(lean_object* v_00_u03b2_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2(v_00_u03b2_2624_, v_x_2625_, v_x_2626_);
lean_dec_ref(v_x_2626_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(lean_object* v_as_2628_, lean_object* v_as_x27_2629_, lean_object* v_b_2630_, lean_object* v_a_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___redArg(v_as_x27_2629_, v_b_2630_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4___boxed(lean_object* v_as_2644_, lean_object* v_as_x27_2645_, lean_object* v_b_2646_, lean_object* v_a_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__4(v_as_2644_, v_as_x27_2645_, v_b_2646_, v_a_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec(v_as_x27_2645_);
lean_dec(v_as_2644_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(lean_object* v_00_u03b2_2660_, lean_object* v_x_2661_, size_t v_x_2662_, lean_object* v_x_2663_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___redArg(v_x_2661_, v_x_2662_, v_x_2663_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2665_, lean_object* v_x_2666_, lean_object* v_x_2667_, lean_object* v_x_2668_){
_start:
{
size_t v_x_19914__boxed_2669_; lean_object* v_res_2670_; 
v_x_19914__boxed_2669_ = lean_unbox_usize(v_x_2667_);
lean_dec(v_x_2667_);
v_res_2670_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1(v_00_u03b2_2665_, v_x_2666_, v_x_19914__boxed_2669_, v_x_2668_);
lean_dec_ref(v_x_2668_);
lean_dec_ref(v_x_2666_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(lean_object* v_00_u03b2_2671_, lean_object* v_x_2672_, size_t v_x_2673_, lean_object* v_x_2674_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___redArg(v_x_2672_, v_x_2673_, v_x_2674_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2676_, lean_object* v_x_2677_, lean_object* v_x_2678_, lean_object* v_x_2679_){
_start:
{
size_t v_x_19925__boxed_2680_; lean_object* v_res_2681_; 
v_x_19925__boxed_2680_ = lean_unbox_usize(v_x_2678_);
lean_dec(v_x_2678_);
v_res_2681_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__2_spec__3(v_00_u03b2_2676_, v_x_2677_, v_x_19925__boxed_2680_, v_x_2679_);
lean_dec_ref(v_x_2679_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2682_, lean_object* v_keys_2683_, lean_object* v_vals_2684_, lean_object* v_heq_2685_, lean_object* v_i_2686_, lean_object* v_k_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___redArg(v_keys_2683_, v_vals_2684_, v_i_2686_, v_k_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2689_, lean_object* v_keys_2690_, lean_object* v_vals_2691_, lean_object* v_heq_2692_, lean_object* v_i_2693_, lean_object* v_k_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts_spec__1_spec__1_spec__2(v_00_u03b2_2689_, v_keys_2690_, v_vals_2691_, v_heq_2692_, v_i_2693_, v_k_2694_);
lean_dec_ref(v_k_2694_);
lean_dec_ref(v_vals_2691_);
lean_dec_ref(v_keys_2690_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(lean_object* v___x_2696_, lean_object* v_keys_2697_, lean_object* v_vals_2698_, lean_object* v_i_2699_, lean_object* v_k_2700_){
_start:
{
lean_object* v___x_2701_; uint8_t v___x_2702_; 
v___x_2701_ = lean_array_get_size(v_keys_2697_);
v___x_2702_ = lean_nat_dec_lt(v_i_2699_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; 
lean_dec_ref(v_k_2700_);
lean_dec(v_i_2699_);
v___x_2703_ = lean_box(0);
return v___x_2703_;
}
else
{
lean_object* v_k_x27_2704_; uint8_t v___x_2705_; 
v_k_x27_2704_ = lean_array_fget_borrowed(v_keys_2697_, v_i_2699_);
lean_inc(v_k_x27_2704_);
lean_inc_ref(v_k_2700_);
v___x_2705_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2696_, v_k_2700_, v_k_x27_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_unsigned_to_nat(1u);
v___x_2707_ = lean_nat_add(v_i_2699_, v___x_2706_);
lean_dec(v_i_2699_);
v_i_2699_ = v___x_2707_;
goto _start;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec_ref(v_k_2700_);
v___x_2709_ = lean_array_fget_borrowed(v_vals_2698_, v_i_2699_);
lean_dec(v_i_2699_);
lean_inc(v___x_2709_);
lean_inc(v_k_x27_2704_);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v_k_x27_2704_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___x_2712_, lean_object* v_keys_2713_, lean_object* v_vals_2714_, lean_object* v_i_2715_, lean_object* v_k_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2712_, v_keys_2713_, v_vals_2714_, v_i_2715_, v_k_2716_);
lean_dec_ref(v_vals_2714_);
lean_dec_ref(v_keys_2713_);
lean_dec_ref(v___x_2712_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(lean_object* v___x_2718_, lean_object* v_x_2719_, size_t v_x_2720_, lean_object* v_x_2721_){
_start:
{
if (lean_obj_tag(v_x_2719_) == 0)
{
lean_object* v_es_2722_; lean_object* v___x_2723_; size_t v___x_2724_; size_t v___x_2725_; lean_object* v_j_2726_; lean_object* v___x_2727_; 
v_es_2722_ = lean_ctor_get(v_x_2719_, 0);
lean_inc_ref(v_es_2722_);
lean_dec_ref_known(v_x_2719_, 1);
v___x_2723_ = lean_box(2);
v___x_2724_ = ((size_t)31ULL);
v___x_2725_ = lean_usize_land(v_x_2720_, v___x_2724_);
v_j_2726_ = lean_usize_to_nat(v___x_2725_);
v___x_2727_ = lean_array_get(v___x_2723_, v_es_2722_, v_j_2726_);
lean_dec(v_j_2726_);
lean_dec_ref(v_es_2722_);
switch(lean_obj_tag(v___x_2727_))
{
case 0:
{
lean_object* v_key_2728_; lean_object* v_val_2729_; uint8_t v___x_2730_; 
v_key_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc_n(v_key_2728_, 2);
v_val_2729_ = lean_ctor_get(v___x_2727_, 1);
lean_inc(v_val_2729_);
lean_dec_ref_known(v___x_2727_, 2);
v___x_2730_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2718_, v_x_2721_, v_key_2728_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_dec(v_val_2729_);
lean_dec(v_key_2728_);
v___x_2731_ = lean_box(0);
return v___x_2731_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_key_2728_);
lean_ctor_set(v___x_2732_, 1, v_val_2729_);
v___x_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
return v___x_2733_;
}
}
case 1:
{
lean_object* v_node_2734_; size_t v___x_2735_; size_t v___x_2736_; 
v_node_2734_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_node_2734_);
lean_dec_ref_known(v___x_2727_, 1);
v___x_2735_ = ((size_t)5ULL);
v___x_2736_ = lean_usize_shift_right(v_x_2720_, v___x_2735_);
v_x_2719_ = v_node_2734_;
v_x_2720_ = v___x_2736_;
goto _start;
}
default: 
{
lean_object* v___x_2738_; 
lean_dec_ref(v_x_2721_);
v___x_2738_ = lean_box(0);
return v___x_2738_;
}
}
}
else
{
lean_object* v_ks_2739_; lean_object* v_vs_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_ks_2739_ = lean_ctor_get(v_x_2719_, 0);
lean_inc_ref(v_ks_2739_);
v_vs_2740_ = lean_ctor_get(v_x_2719_, 1);
lean_inc_ref(v_vs_2740_);
lean_dec_ref_known(v_x_2719_, 2);
v___x_2741_ = lean_unsigned_to_nat(0u);
v___x_2742_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_2718_, v_ks_2739_, v_vs_2740_, v___x_2741_, v_x_2721_);
lean_dec_ref(v_vs_2740_);
lean_dec_ref(v_ks_2739_);
return v___x_2742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg___boxed(lean_object* v___x_2743_, lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_){
_start:
{
size_t v_x_25943__boxed_2747_; lean_object* v_res_2748_; 
v_x_25943__boxed_2747_ = lean_unbox_usize(v_x_2745_);
lean_dec(v_x_2745_);
v_res_2748_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2743_, v_x_2744_, v_x_25943__boxed_2747_, v_x_2746_);
lean_dec_ref(v___x_2743_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(lean_object* v___x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_){
_start:
{
uint64_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
lean_inc_ref(v_x_2751_);
v___x_2752_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2749_, v_x_2751_);
v___x_2753_ = lean_uint64_to_usize(v___x_2752_);
lean_inc_ref(v_x_2750_);
v___x_2754_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_2749_, v_x_2750_, v___x_2753_, v_x_2751_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg___boxed(lean_object* v___x_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_2755_, v_x_2756_, v_x_2757_);
lean_dec_ref(v_x_2756_);
lean_dec_ref(v___x_2755_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v___x_2759_, lean_object* v_x_2760_, lean_object* v_x_2761_, lean_object* v_x_2762_, lean_object* v_x_2763_){
_start:
{
lean_object* v_ks_2764_; lean_object* v_vs_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2789_; 
v_ks_2764_ = lean_ctor_get(v_x_2760_, 0);
v_vs_2765_ = lean_ctor_get(v_x_2760_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_x_2760_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2767_ = v_x_2760_;
v_isShared_2768_ = v_isSharedCheck_2789_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_vs_2765_);
lean_inc(v_ks_2764_);
lean_dec(v_x_2760_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2789_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2769_ = lean_array_get_size(v_ks_2764_);
v___x_2770_ = lean_nat_dec_lt(v_x_2761_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec(v_x_2761_);
v___x_2771_ = lean_array_push(v_ks_2764_, v_x_2762_);
v___x_2772_ = lean_array_push(v_vs_2765_, v_x_2763_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 1, v___x_2772_);
lean_ctor_set(v___x_2767_, 0, v___x_2771_);
v___x_2774_ = v___x_2767_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
else
{
lean_object* v_k_x27_2776_; uint8_t v___x_2777_; 
v_k_x27_2776_ = lean_array_fget_borrowed(v_ks_2764_, v_x_2761_);
lean_inc(v_k_x27_2776_);
lean_inc_ref(v_x_2762_);
v___x_2777_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2759_, v_x_2762_, v_k_x27_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2779_; 
if (v_isShared_2768_ == 0)
{
v___x_2779_ = v___x_2767_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_ks_2764_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_vs_2765_);
v___x_2779_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_unsigned_to_nat(1u);
v___x_2781_ = lean_nat_add(v_x_2761_, v___x_2780_);
lean_dec(v_x_2761_);
v_x_2760_ = v___x_2779_;
v_x_2761_ = v___x_2781_;
goto _start;
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2784_ = lean_array_fset(v_ks_2764_, v_x_2761_, v_x_2762_);
v___x_2785_ = lean_array_fset(v_vs_2765_, v_x_2761_, v_x_2763_);
lean_dec(v_x_2761_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 1, v___x_2785_);
lean_ctor_set(v___x_2767_, 0, v___x_2784_);
v___x_2787_ = v___x_2767_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___x_2790_, lean_object* v_x_2791_, lean_object* v_x_2792_, lean_object* v_x_2793_, lean_object* v_x_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2790_, v_x_2791_, v_x_2792_, v_x_2793_, v_x_2794_);
lean_dec_ref(v___x_2790_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(lean_object* v___x_2796_, lean_object* v_n_2797_, lean_object* v_k_2798_, lean_object* v_v_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_unsigned_to_nat(0u);
v___x_2801_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_2796_, v_n_2797_, v___x_2800_, v_k_2798_, v_v_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___x_2802_, lean_object* v_n_2803_, lean_object* v_k_2804_, lean_object* v_v_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2802_, v_n_2803_, v_k_2804_, v_v_2805_);
lean_dec_ref(v___x_2802_);
return v_res_2806_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(lean_object* v___x_2808_, lean_object* v_x_2809_, size_t v_x_2810_, size_t v_x_2811_, lean_object* v_x_2812_, lean_object* v_x_2813_){
_start:
{
if (lean_obj_tag(v_x_2809_) == 0)
{
lean_object* v_es_2814_; size_t v___x_2815_; size_t v___x_2816_; lean_object* v_j_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v_es_2814_ = lean_ctor_get(v_x_2809_, 0);
v___x_2815_ = ((size_t)31ULL);
v___x_2816_ = lean_usize_land(v_x_2810_, v___x_2815_);
v_j_2817_ = lean_usize_to_nat(v___x_2816_);
v___x_2818_ = lean_array_get_size(v_es_2814_);
v___x_2819_ = lean_nat_dec_lt(v_j_2817_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_dec(v_j_2817_);
lean_dec(v_x_2813_);
lean_dec_ref(v_x_2812_);
return v_x_2809_;
}
else
{
lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2858_; 
lean_inc_ref(v_es_2814_);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_x_2809_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v_x_2809_, 0);
lean_dec(v_unused_2859_);
v___x_2821_ = v_x_2809_;
v_isShared_2822_ = v_isSharedCheck_2858_;
goto v_resetjp_2820_;
}
else
{
lean_dec(v_x_2809_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2858_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v_v_2823_; lean_object* v___x_2824_; lean_object* v_xs_x27_2825_; lean_object* v___y_2827_; 
v_v_2823_ = lean_array_fget(v_es_2814_, v_j_2817_);
v___x_2824_ = lean_box(0);
v_xs_x27_2825_ = lean_array_fset(v_es_2814_, v_j_2817_, v___x_2824_);
switch(lean_obj_tag(v_v_2823_))
{
case 0:
{
lean_object* v_key_2832_; lean_object* v_val_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2843_; 
v_key_2832_ = lean_ctor_get(v_v_2823_, 0);
v_val_2833_ = lean_ctor_get(v_v_2823_, 1);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_v_2823_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2835_ = v_v_2823_;
v_isShared_2836_ = v_isSharedCheck_2843_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_val_2833_);
lean_inc(v_key_2832_);
lean_dec(v_v_2823_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2843_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
uint8_t v___x_2837_; 
lean_inc(v_key_2832_);
lean_inc_ref(v_x_2812_);
v___x_2837_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_2808_, v_x_2812_, v_key_2832_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_del_object(v___x_2835_);
v___x_2838_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2832_, v_val_2833_, v_x_2812_, v_x_2813_);
v___x_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
v___y_2827_ = v___x_2839_;
goto v___jp_2826_;
}
else
{
lean_object* v___x_2841_; 
lean_dec(v_val_2833_);
lean_dec(v_key_2832_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 1, v_x_2813_);
lean_ctor_set(v___x_2835_, 0, v_x_2812_);
v___x_2841_ = v___x_2835_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_x_2812_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_x_2813_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
v___y_2827_ = v___x_2841_;
goto v___jp_2826_;
}
}
}
}
case 1:
{
lean_object* v_node_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2856_; 
v_node_2844_ = lean_ctor_get(v_v_2823_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_v_2823_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2846_ = v_v_2823_;
v_isShared_2847_ = v_isSharedCheck_2856_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_node_2844_);
lean_dec(v_v_2823_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2856_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
size_t v___x_2848_; size_t v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2848_ = ((size_t)5ULL);
v___x_2849_ = lean_usize_shift_right(v_x_2810_, v___x_2848_);
v___x_2850_ = ((size_t)1ULL);
v___x_2851_ = lean_usize_add(v_x_2811_, v___x_2850_);
v___x_2852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2808_, v_node_2844_, v___x_2849_, v___x_2851_, v_x_2812_, v_x_2813_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2852_);
v___x_2854_ = v___x_2846_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
v___y_2827_ = v___x_2854_;
goto v___jp_2826_;
}
}
}
default: 
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v_x_2812_);
lean_ctor_set(v___x_2857_, 1, v_x_2813_);
v___y_2827_ = v___x_2857_;
goto v___jp_2826_;
}
}
v___jp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2828_ = lean_array_fset(v_xs_x27_2825_, v_j_2817_, v___y_2827_);
lean_dec(v_j_2817_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2828_);
v___x_2830_ = v___x_2821_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
else
{
lean_object* v_ks_2860_; lean_object* v_vs_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2879_; 
v_ks_2860_ = lean_ctor_get(v_x_2809_, 0);
v_vs_2861_ = lean_ctor_get(v_x_2809_, 1);
v_isSharedCheck_2879_ = !lean_is_exclusive(v_x_2809_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2863_ = v_x_2809_;
v_isShared_2864_ = v_isSharedCheck_2879_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_vs_2861_);
lean_inc(v_ks_2860_);
lean_dec(v_x_2809_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2879_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_ks_2860_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_vs_2861_);
v___x_2866_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v_newNode_2867_; size_t v___x_2868_; uint8_t v___x_2869_; 
v_newNode_2867_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_2808_, v___x_2866_, v_x_2812_, v_x_2813_);
v___x_2868_ = ((size_t)7ULL);
v___x_2869_ = lean_usize_dec_le(v___x_2868_, v_x_2811_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2870_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2867_);
v___x_2871_ = lean_unsigned_to_nat(4u);
v___x_2872_ = lean_nat_dec_lt(v___x_2870_, v___x_2871_);
lean_dec(v___x_2870_);
if (v___x_2872_ == 0)
{
lean_object* v_ks_2873_; lean_object* v_vs_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_ks_2873_ = lean_ctor_get(v_newNode_2867_, 0);
lean_inc_ref(v_ks_2873_);
v_vs_2874_ = lean_ctor_get(v_newNode_2867_, 1);
lean_inc_ref(v_vs_2874_);
lean_dec_ref(v_newNode_2867_);
v___x_2875_ = lean_unsigned_to_nat(0u);
v___x_2876_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___closed__0);
v___x_2877_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2808_, v_x_2811_, v_ks_2873_, v_vs_2874_, v___x_2875_, v___x_2876_);
lean_dec_ref(v_vs_2874_);
lean_dec_ref(v_ks_2873_);
return v___x_2877_;
}
else
{
return v_newNode_2867_;
}
}
else
{
return v_newNode_2867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(lean_object* v___x_2880_, size_t v_depth_2881_, lean_object* v_keys_2882_, lean_object* v_vals_2883_, lean_object* v_i_2884_, lean_object* v_entries_2885_){
_start:
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = lean_array_get_size(v_keys_2882_);
v___x_2887_ = lean_nat_dec_lt(v_i_2884_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_dec(v_i_2884_);
return v_entries_2885_;
}
else
{
lean_object* v_k_2888_; lean_object* v_v_2889_; uint64_t v___x_2890_; size_t v_h_2891_; size_t v___x_2892_; lean_object* v___x_2893_; size_t v___x_2894_; size_t v___x_2895_; size_t v___x_2896_; size_t v_h_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_k_2888_ = lean_array_fget_borrowed(v_keys_2882_, v_i_2884_);
v_v_2889_ = lean_array_fget_borrowed(v_vals_2883_, v_i_2884_);
lean_inc_n(v_k_2888_, 2);
v___x_2890_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2880_, v_k_2888_);
v_h_2891_ = lean_uint64_to_usize(v___x_2890_);
v___x_2892_ = ((size_t)5ULL);
v___x_2893_ = lean_unsigned_to_nat(1u);
v___x_2894_ = ((size_t)1ULL);
v___x_2895_ = lean_usize_sub(v_depth_2881_, v___x_2894_);
v___x_2896_ = lean_usize_mul(v___x_2892_, v___x_2895_);
v_h_2897_ = lean_usize_shift_right(v_h_2891_, v___x_2896_);
v___x_2898_ = lean_nat_add(v_i_2884_, v___x_2893_);
lean_dec(v_i_2884_);
lean_inc(v_v_2889_);
v___x_2899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2880_, v_entries_2885_, v_h_2897_, v_depth_2881_, v_k_2888_, v_v_2889_);
v_i_2884_ = v___x_2898_;
v_entries_2885_ = v___x_2899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___x_2901_, lean_object* v_depth_2902_, lean_object* v_keys_2903_, lean_object* v_vals_2904_, lean_object* v_i_2905_, lean_object* v_entries_2906_){
_start:
{
size_t v_depth_boxed_2907_; lean_object* v_res_2908_; 
v_depth_boxed_2907_ = lean_unbox_usize(v_depth_2902_);
lean_dec(v_depth_2902_);
v_res_2908_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_2901_, v_depth_boxed_2907_, v_keys_2903_, v_vals_2904_, v_i_2905_, v_entries_2906_);
lean_dec_ref(v_vals_2904_);
lean_dec_ref(v_keys_2903_);
lean_dec_ref(v___x_2901_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg___boxed(lean_object* v___x_2909_, lean_object* v_x_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
size_t v_x_26097__boxed_2915_; size_t v_x_26098__boxed_2916_; lean_object* v_res_2917_; 
v_x_26097__boxed_2915_ = lean_unbox_usize(v_x_2911_);
lean_dec(v_x_2911_);
v_x_26098__boxed_2916_ = lean_unbox_usize(v_x_2912_);
lean_dec(v_x_2912_);
v_res_2917_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2909_, v_x_2910_, v_x_26097__boxed_2915_, v_x_26098__boxed_2916_, v_x_2913_, v_x_2914_);
lean_dec_ref(v___x_2909_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(lean_object* v___x_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_, lean_object* v_x_2921_){
_start:
{
uint64_t v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
lean_inc_ref(v_x_2920_);
v___x_2922_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_2918_, v_x_2920_);
v___x_2923_ = lean_uint64_to_usize(v___x_2922_);
v___x_2924_ = ((size_t)1ULL);
v___x_2925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_2918_, v_x_2919_, v___x_2923_, v___x_2924_, v_x_2920_, v_x_2921_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg___boxed(lean_object* v___x_2926_, lean_object* v_x_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_2926_, v_x_2927_, v_x_2928_, v_x_2929_);
lean_dec_ref(v___x_2926_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(lean_object* v_lhs_2935_, lean_object* v_rootNew_2936_, uint8_t v_a_2937_, lean_object* v_a_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; lean_object* v_snd_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_3116_; 
v___x_2946_ = lean_st_ref_get(v___y_2939_);
v_snd_2947_ = lean_ctor_get(v_a_2938_, 1);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v_a_2938_, 0);
lean_dec(v_unused_3117_);
v___x_2949_ = v_a_2938_;
v_isShared_2950_ = v_isSharedCheck_3116_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_snd_2947_);
lean_dec(v_a_2938_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_3116_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; 
lean_inc(v_snd_2947_);
v___x_2951_ = l_Lean_Meta_Grind_Goal_getENode(v___x_2946_, v_snd_2947_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___x_2946_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_3107_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_3107_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_3107_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v_self_2956_; lean_object* v_next_2957_; lean_object* v_congr_2958_; lean_object* v_target_x3f_2959_; lean_object* v_proof_x3f_2960_; uint8_t v_flipped_2961_; lean_object* v_size_2962_; uint8_t v_interpreted_2963_; uint8_t v_ctor_2964_; uint8_t v_hasLambdas_2965_; uint8_t v_heqProofs_2966_; lean_object* v_idx_2967_; lean_object* v_generation_2968_; lean_object* v_mt_2969_; lean_object* v_sTerms_2970_; uint8_t v_funCC_2971_; lean_object* v_ematchDiagSource_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_3105_; 
v_self_2956_ = lean_ctor_get(v_a_2952_, 0);
v_next_2957_ = lean_ctor_get(v_a_2952_, 1);
v_congr_2958_ = lean_ctor_get(v_a_2952_, 3);
v_target_x3f_2959_ = lean_ctor_get(v_a_2952_, 4);
v_proof_x3f_2960_ = lean_ctor_get(v_a_2952_, 5);
v_flipped_2961_ = lean_ctor_get_uint8(v_a_2952_, sizeof(void*)*12);
v_size_2962_ = lean_ctor_get(v_a_2952_, 6);
v_interpreted_2963_ = lean_ctor_get_uint8(v_a_2952_, sizeof(void*)*12 + 1);
v_ctor_2964_ = lean_ctor_get_uint8(v_a_2952_, sizeof(void*)*12 + 2);
v_hasLambdas_2965_ = lean_ctor_get_uint8(v_a_2952_, sizeof(void*)*12 + 3);
v_heqProofs_2966_ = lean_ctor_get_uint8(v_a_2952_, sizeof(void*)*12 + 4);
v_idx_2967_ = lean_ctor_get(v_a_2952_, 7);
v_generation_2968_ = lean_ctor_get(v_a_2952_, 8);
v_mt_2969_ = lean_ctor_get(v_a_2952_, 9);
v_sTerms_2970_ = lean_ctor_get(v_a_2952_, 10);
v_funCC_2971_ = lean_ctor_get_uint8(v_a_2952_, sizeof(void*)*12 + 5);
v_ematchDiagSource_2972_ = lean_ctor_get(v_a_2952_, 11);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_a_2952_);
if (v_isSharedCheck_3105_ == 0)
{
lean_object* v_unused_3106_; 
v_unused_3106_ = lean_ctor_get(v_a_2952_, 2);
lean_dec(v_unused_3106_);
v___x_2974_ = v_a_2952_;
v_isShared_2975_ = v_isSharedCheck_3105_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_ematchDiagSource_2972_);
lean_inc(v_sTerms_2970_);
lean_inc(v_mt_2969_);
lean_inc(v_generation_2968_);
lean_inc(v_idx_2967_);
lean_inc(v_size_2962_);
lean_inc(v_proof_x3f_2960_);
lean_inc(v_target_x3f_2959_);
lean_inc(v_congr_2958_);
lean_inc(v_next_2957_);
lean_inc(v_self_2956_);
lean_dec(v_a_2952_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_3105_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2976_; lean_object* v___y_2993_; lean_object* v___x_3003_; 
v___x_2976_ = lean_box(0);
lean_inc(v_ematchDiagSource_2972_);
lean_inc(v_sTerms_2970_);
lean_inc(v_mt_2969_);
lean_inc(v_generation_2968_);
lean_inc(v_idx_2967_);
lean_inc(v_size_2962_);
lean_inc(v_proof_x3f_2960_);
lean_inc(v_target_x3f_2959_);
lean_inc_ref(v_rootNew_2936_);
lean_inc_ref(v_next_2957_);
lean_inc_ref(v_self_2956_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 2, v_rootNew_2936_);
v___x_3003_ = v___x_2974_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_self_2956_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_next_2957_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_rootNew_2936_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_congr_2958_);
lean_ctor_set(v_reuseFailAlloc_3104_, 4, v_target_x3f_2959_);
lean_ctor_set(v_reuseFailAlloc_3104_, 5, v_proof_x3f_2960_);
lean_ctor_set(v_reuseFailAlloc_3104_, 6, v_size_2962_);
lean_ctor_set(v_reuseFailAlloc_3104_, 7, v_idx_2967_);
lean_ctor_set(v_reuseFailAlloc_3104_, 8, v_generation_2968_);
lean_ctor_set(v_reuseFailAlloc_3104_, 9, v_mt_2969_);
lean_ctor_set(v_reuseFailAlloc_3104_, 10, v_sTerms_2970_);
lean_ctor_set(v_reuseFailAlloc_3104_, 11, v_ematchDiagSource_2972_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12, v_flipped_2961_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12 + 1, v_interpreted_2963_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12 + 2, v_ctor_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12 + 3, v_hasLambdas_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12 + 4, v_heqProofs_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_3104_, sizeof(void*)*12 + 5, v_funCC_2971_);
v___x_3003_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3002_;
}
v___jp_2977_:
{
size_t v___x_2978_; size_t v___x_2979_; uint8_t v___x_2980_; 
v___x_2978_ = lean_ptr_addr(v_next_2957_);
v___x_2979_ = lean_ptr_addr(v_lhs_2935_);
v___x_2980_ = lean_usize_dec_eq(v___x_2978_, v___x_2979_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2982_; 
lean_del_object(v___x_2954_);
lean_dec(v_snd_2947_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v_next_2957_);
lean_ctor_set(v___x_2949_, 0, v___x_2976_);
v___x_2982_ = v___x_2949_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2976_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_next_2957_);
v___x_2982_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
v_a_2938_ = v___x_2982_;
goto _start;
}
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
lean_dec_ref(v_next_2957_);
lean_dec_ref(v_rootNew_2936_);
v___x_2985_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__0));
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2985_);
v___x_2987_ = v___x_2949_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_snd_2947_);
v___x_2987_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2989_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2987_);
v___x_2989_ = v___x_2954_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
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
v___jp_2992_:
{
if (lean_obj_tag(v___y_2993_) == 0)
{
lean_dec_ref_known(v___y_2993_, 1);
goto v___jp_2977_;
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec_ref(v_next_2957_);
lean_del_object(v___x_2954_);
lean_del_object(v___x_2949_);
lean_dec(v_snd_2947_);
lean_dec_ref(v_rootNew_2936_);
v_a_2994_ = lean_ctor_get(v___y_2993_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___y_2993_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___y_2993_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___y_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; 
lean_inc_ref(v___x_3003_);
lean_inc_ref(v_self_2956_);
v___x_3004_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2956_, v___x_3003_, v___y_2939_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_dec_ref_known(v___x_3004_, 1);
if (v_a_2937_ == 0)
{
lean_dec_ref(v___x_3003_);
lean_dec(v_ematchDiagSource_2972_);
lean_dec(v_sTerms_2970_);
lean_dec(v_mt_2969_);
lean_dec(v_generation_2968_);
lean_dec(v_idx_2967_);
lean_dec(v_size_2962_);
lean_dec(v_proof_x3f_2960_);
lean_dec(v_target_x3f_2959_);
lean_dec_ref(v_self_2956_);
goto v___jp_2977_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3005_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_3006_ = lean_unsigned_to_nat(3u);
v___x_3007_ = l_Lean_Expr_isAppOfArity(v_self_2956_, v___x_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_dec_ref(v___x_3003_);
lean_dec(v_ematchDiagSource_2972_);
lean_dec(v_sTerms_2970_);
lean_dec(v_mt_2969_);
lean_dec(v_generation_2968_);
lean_dec(v_idx_2967_);
lean_dec(v_size_2962_);
lean_dec(v_proof_x3f_2960_);
lean_dec(v_target_x3f_2959_);
lean_dec_ref(v_self_2956_);
goto v___jp_2977_;
}
else
{
uint8_t v___x_3008_; 
v___x_3008_ = l_Lean_Meta_Grind_ENode_isCongrRoot(v___x_3003_);
lean_dec_ref(v___x_3003_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v_toGoalState_3010_; lean_object* v_enodeMap_3011_; lean_object* v_congrTable_3012_; lean_object* v___x_3013_; 
v___x_3009_ = lean_st_ref_get(v___y_2939_);
v_toGoalState_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc_ref(v_toGoalState_3010_);
lean_dec(v___x_3009_);
v_enodeMap_3011_ = lean_ctor_get(v_toGoalState_3010_, 1);
lean_inc_ref(v_enodeMap_3011_);
v_congrTable_3012_ = lean_ctor_get(v_toGoalState_3010_, 4);
lean_inc_ref(v_congrTable_3012_);
lean_dec_ref(v_toGoalState_3010_);
lean_inc_ref(v_self_2956_);
v___x_3013_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v_enodeMap_3011_, v_congrTable_3012_, v_self_2956_);
lean_dec_ref(v_congrTable_3012_);
lean_dec_ref(v_enodeMap_3011_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_dec(v_ematchDiagSource_2972_);
lean_dec(v_sTerms_2970_);
lean_dec(v_mt_2969_);
lean_dec(v_generation_2968_);
lean_dec(v_idx_2967_);
lean_dec(v_size_2962_);
lean_dec(v_proof_x3f_2960_);
lean_dec(v_target_x3f_2959_);
lean_dec_ref(v_self_2956_);
goto v___jp_2977_;
}
else
{
lean_object* v_val_3014_; lean_object* v_fst_3015_; lean_object* v___x_3016_; 
v_val_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_val_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v_fst_3015_ = lean_ctor_get(v_val_3014_, 0);
lean_inc(v_fst_3015_);
lean_dec(v_val_3014_);
v___x_3016_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_fst_3015_, v___y_2940_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; uint8_t v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = lean_unbox(v_a_3017_);
lean_dec(v_a_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v_toGoalState_3020_; lean_object* v_mvarId_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3095_; 
v___x_3019_ = lean_st_ref_take(v___y_2939_);
v_toGoalState_3020_ = lean_ctor_get(v___x_3019_, 0);
v_mvarId_3021_ = lean_ctor_get(v___x_3019_, 1);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3023_ = v___x_3019_;
v_isShared_3024_ = v_isSharedCheck_3095_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_mvarId_3021_);
lean_inc(v_toGoalState_3020_);
lean_dec(v___x_3019_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3095_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v_nextDeclIdx_3025_; lean_object* v_enodeMap_3026_; lean_object* v_exprs_3027_; lean_object* v_parents_3028_; lean_object* v_congrTable_3029_; lean_object* v_appMap_3030_; lean_object* v_indicesFound_3031_; lean_object* v_newFacts_3032_; uint8_t v_inconsistent_3033_; lean_object* v_nextIdx_3034_; lean_object* v_newRawFacts_3035_; lean_object* v_facts_3036_; lean_object* v_extThms_3037_; lean_object* v_ematch_3038_; lean_object* v_inj_3039_; lean_object* v_split_3040_; lean_object* v_clean_3041_; lean_object* v_sstates_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3094_; 
v_nextDeclIdx_3025_ = lean_ctor_get(v_toGoalState_3020_, 0);
v_enodeMap_3026_ = lean_ctor_get(v_toGoalState_3020_, 1);
v_exprs_3027_ = lean_ctor_get(v_toGoalState_3020_, 2);
v_parents_3028_ = lean_ctor_get(v_toGoalState_3020_, 3);
v_congrTable_3029_ = lean_ctor_get(v_toGoalState_3020_, 4);
v_appMap_3030_ = lean_ctor_get(v_toGoalState_3020_, 5);
v_indicesFound_3031_ = lean_ctor_get(v_toGoalState_3020_, 6);
v_newFacts_3032_ = lean_ctor_get(v_toGoalState_3020_, 7);
v_inconsistent_3033_ = lean_ctor_get_uint8(v_toGoalState_3020_, sizeof(void*)*17);
v_nextIdx_3034_ = lean_ctor_get(v_toGoalState_3020_, 8);
v_newRawFacts_3035_ = lean_ctor_get(v_toGoalState_3020_, 9);
v_facts_3036_ = lean_ctor_get(v_toGoalState_3020_, 10);
v_extThms_3037_ = lean_ctor_get(v_toGoalState_3020_, 11);
v_ematch_3038_ = lean_ctor_get(v_toGoalState_3020_, 12);
v_inj_3039_ = lean_ctor_get(v_toGoalState_3020_, 13);
v_split_3040_ = lean_ctor_get(v_toGoalState_3020_, 14);
v_clean_3041_ = lean_ctor_get(v_toGoalState_3020_, 15);
v_sstates_3042_ = lean_ctor_get(v_toGoalState_3020_, 16);
v_isSharedCheck_3094_ = !lean_is_exclusive(v_toGoalState_3020_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3044_ = v_toGoalState_3020_;
v_isShared_3045_ = v_isSharedCheck_3094_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_sstates_3042_);
lean_inc(v_clean_3041_);
lean_inc(v_split_3040_);
lean_inc(v_inj_3039_);
lean_inc(v_ematch_3038_);
lean_inc(v_extThms_3037_);
lean_inc(v_facts_3036_);
lean_inc(v_newRawFacts_3035_);
lean_inc(v_nextIdx_3034_);
lean_inc(v_newFacts_3032_);
lean_inc(v_indicesFound_3031_);
lean_inc(v_appMap_3030_);
lean_inc(v_congrTable_3029_);
lean_inc(v_parents_3028_);
lean_inc(v_exprs_3027_);
lean_inc(v_enodeMap_3026_);
lean_inc(v_nextDeclIdx_3025_);
lean_dec(v_toGoalState_3020_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3094_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3046_ = lean_box(0);
lean_inc_ref(v_self_2956_);
v___x_3047_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v_enodeMap_3026_, v_congrTable_3029_, v_self_2956_, v___x_3046_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 4, v___x_3047_);
v___x_3049_ = v___x_3044_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_nextDeclIdx_3025_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_enodeMap_3026_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v_exprs_3027_);
lean_ctor_set(v_reuseFailAlloc_3093_, 3, v_parents_3028_);
lean_ctor_set(v_reuseFailAlloc_3093_, 4, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3093_, 5, v_appMap_3030_);
lean_ctor_set(v_reuseFailAlloc_3093_, 6, v_indicesFound_3031_);
lean_ctor_set(v_reuseFailAlloc_3093_, 7, v_newFacts_3032_);
lean_ctor_set(v_reuseFailAlloc_3093_, 8, v_nextIdx_3034_);
lean_ctor_set(v_reuseFailAlloc_3093_, 9, v_newRawFacts_3035_);
lean_ctor_set(v_reuseFailAlloc_3093_, 10, v_facts_3036_);
lean_ctor_set(v_reuseFailAlloc_3093_, 11, v_extThms_3037_);
lean_ctor_set(v_reuseFailAlloc_3093_, 12, v_ematch_3038_);
lean_ctor_set(v_reuseFailAlloc_3093_, 13, v_inj_3039_);
lean_ctor_set(v_reuseFailAlloc_3093_, 14, v_split_3040_);
lean_ctor_set(v_reuseFailAlloc_3093_, 15, v_clean_3041_);
lean_ctor_set(v_reuseFailAlloc_3093_, 16, v_sstates_3042_);
lean_ctor_set_uint8(v_reuseFailAlloc_3093_, sizeof(void*)*17, v_inconsistent_3033_);
v___x_3049_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3051_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 0, v___x_3049_);
v___x_3051_ = v___x_3023_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_mvarId_3021_);
v___x_3051_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = lean_st_ref_put(v___y_2939_, v___x_3051_);
lean_inc_ref(v_rootNew_2936_);
lean_inc_ref(v_next_2957_);
lean_inc_ref_n(v_self_2956_, 3);
v___x_3053_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3053_, 0, v_self_2956_);
lean_ctor_set(v___x_3053_, 1, v_next_2957_);
lean_ctor_set(v___x_3053_, 2, v_rootNew_2936_);
lean_ctor_set(v___x_3053_, 3, v_self_2956_);
lean_ctor_set(v___x_3053_, 4, v_target_x3f_2959_);
lean_ctor_set(v___x_3053_, 5, v_proof_x3f_2960_);
lean_ctor_set(v___x_3053_, 6, v_size_2962_);
lean_ctor_set(v___x_3053_, 7, v_idx_2967_);
lean_ctor_set(v___x_3053_, 8, v_generation_2968_);
lean_ctor_set(v___x_3053_, 9, v_mt_2969_);
lean_ctor_set(v___x_3053_, 10, v_sTerms_2970_);
lean_ctor_set(v___x_3053_, 11, v_ematchDiagSource_2972_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12, v_flipped_2961_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12 + 1, v_interpreted_2963_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12 + 2, v_ctor_2964_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12 + 3, v_hasLambdas_2965_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12 + 4, v_heqProofs_2966_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*12 + 5, v_funCC_2971_);
v___x_3054_ = l_Lean_Meta_Grind_setENode___redArg(v_self_2956_, v___x_3053_, v___y_2939_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_dec_ref_known(v___x_3054_, 1);
v___x_3055_ = lean_st_ref_get(v___y_2939_);
lean_inc(v_fst_3015_);
v___x_3056_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3055_, v_fst_3015_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___x_3055_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v_self_3058_; lean_object* v_next_3059_; lean_object* v_root_3060_; lean_object* v_target_x3f_3061_; lean_object* v_proof_x3f_3062_; uint8_t v_flipped_3063_; lean_object* v_size_3064_; uint8_t v_interpreted_3065_; uint8_t v_ctor_3066_; uint8_t v_hasLambdas_3067_; uint8_t v_heqProofs_3068_; lean_object* v_idx_3069_; lean_object* v_generation_3070_; lean_object* v_mt_3071_; lean_object* v_sTerms_3072_; uint8_t v_funCC_3073_; lean_object* v_ematchDiagSource_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3082_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v_self_3058_ = lean_ctor_get(v_a_3057_, 0);
v_next_3059_ = lean_ctor_get(v_a_3057_, 1);
v_root_3060_ = lean_ctor_get(v_a_3057_, 2);
v_target_x3f_3061_ = lean_ctor_get(v_a_3057_, 4);
v_proof_x3f_3062_ = lean_ctor_get(v_a_3057_, 5);
v_flipped_3063_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12);
v_size_3064_ = lean_ctor_get(v_a_3057_, 6);
v_interpreted_3065_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12 + 1);
v_ctor_3066_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12 + 2);
v_hasLambdas_3067_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12 + 3);
v_heqProofs_3068_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12 + 4);
v_idx_3069_ = lean_ctor_get(v_a_3057_, 7);
v_generation_3070_ = lean_ctor_get(v_a_3057_, 8);
v_mt_3071_ = lean_ctor_get(v_a_3057_, 9);
v_sTerms_3072_ = lean_ctor_get(v_a_3057_, 10);
v_funCC_3073_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3074_ = lean_ctor_get(v_a_3057_, 11);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_a_3057_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v_a_3057_, 3);
lean_dec(v_unused_3083_);
v___x_3076_ = v_a_3057_;
v_isShared_3077_ = v_isSharedCheck_3082_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_ematchDiagSource_3074_);
lean_inc(v_sTerms_3072_);
lean_inc(v_mt_3071_);
lean_inc(v_generation_3070_);
lean_inc(v_idx_3069_);
lean_inc(v_size_3064_);
lean_inc(v_proof_x3f_3062_);
lean_inc(v_target_x3f_3061_);
lean_inc(v_root_3060_);
lean_inc(v_next_3059_);
lean_inc(v_self_3058_);
lean_dec(v_a_3057_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3082_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 3, v_self_2956_);
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_self_3058_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v_next_3059_);
lean_ctor_set(v_reuseFailAlloc_3081_, 2, v_root_3060_);
lean_ctor_set(v_reuseFailAlloc_3081_, 3, v_self_2956_);
lean_ctor_set(v_reuseFailAlloc_3081_, 4, v_target_x3f_3061_);
lean_ctor_set(v_reuseFailAlloc_3081_, 5, v_proof_x3f_3062_);
lean_ctor_set(v_reuseFailAlloc_3081_, 6, v_size_3064_);
lean_ctor_set(v_reuseFailAlloc_3081_, 7, v_idx_3069_);
lean_ctor_set(v_reuseFailAlloc_3081_, 8, v_generation_3070_);
lean_ctor_set(v_reuseFailAlloc_3081_, 9, v_mt_3071_);
lean_ctor_set(v_reuseFailAlloc_3081_, 10, v_sTerms_3072_);
lean_ctor_set(v_reuseFailAlloc_3081_, 11, v_ematchDiagSource_3074_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12, v_flipped_3063_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 1, v_interpreted_3065_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 2, v_ctor_3066_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 3, v_hasLambdas_3067_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 4, v_heqProofs_3068_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*12 + 5, v_funCC_3073_);
v___x_3079_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lean_Meta_Grind_setENode___redArg(v_fst_3015_, v___x_3079_, v___y_2939_);
v___y_2993_ = v___x_3080_;
goto v___jp_2992_;
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_fst_3015_);
lean_dec_ref(v_next_2957_);
lean_dec_ref(v_self_2956_);
lean_del_object(v___x_2954_);
lean_del_object(v___x_2949_);
lean_dec(v_snd_2947_);
lean_dec_ref(v_rootNew_2936_);
v_a_3084_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3056_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3056_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_dec(v_fst_3015_);
lean_dec_ref(v_self_2956_);
v___y_2993_ = v___x_3054_;
goto v___jp_2992_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_3015_);
lean_dec(v_ematchDiagSource_2972_);
lean_dec(v_sTerms_2970_);
lean_dec(v_mt_2969_);
lean_dec(v_generation_2968_);
lean_dec(v_idx_2967_);
lean_dec(v_size_2962_);
lean_dec(v_proof_x3f_2960_);
lean_dec(v_target_x3f_2959_);
lean_dec_ref(v_self_2956_);
goto v___jp_2977_;
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_fst_3015_);
lean_dec(v_ematchDiagSource_2972_);
lean_dec(v_sTerms_2970_);
lean_dec(v_mt_2969_);
lean_dec(v_generation_2968_);
lean_dec(v_idx_2967_);
lean_dec(v_size_2962_);
lean_dec(v_proof_x3f_2960_);
lean_dec(v_target_x3f_2959_);
lean_dec_ref(v_next_2957_);
lean_dec_ref(v_self_2956_);
lean_del_object(v___x_2954_);
lean_del_object(v___x_2949_);
lean_dec(v_snd_2947_);
lean_dec_ref(v_rootNew_2936_);
v_a_3096_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3016_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3016_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
else
{
lean_dec(v_ematchDiagSource_2972_);
lean_dec(v_sTerms_2970_);
lean_dec(v_mt_2969_);
lean_dec(v_generation_2968_);
lean_dec(v_idx_2967_);
lean_dec(v_size_2962_);
lean_dec(v_proof_x3f_2960_);
lean_dec(v_target_x3f_2959_);
lean_dec_ref(v_self_2956_);
goto v___jp_2977_;
}
}
}
}
else
{
lean_dec_ref(v___x_3003_);
lean_dec(v_ematchDiagSource_2972_);
lean_dec(v_sTerms_2970_);
lean_dec(v_mt_2969_);
lean_dec(v_generation_2968_);
lean_dec(v_idx_2967_);
lean_dec(v_size_2962_);
lean_dec(v_proof_x3f_2960_);
lean_dec(v_target_x3f_2959_);
lean_dec_ref(v_self_2956_);
v___y_2993_ = v___x_3004_;
goto v___jp_2992_;
}
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_del_object(v___x_2949_);
lean_dec(v_snd_2947_);
lean_dec_ref(v_rootNew_2936_);
v_a_3108_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_2951_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_2951_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___boxed(lean_object* v_lhs_3118_, lean_object* v_rootNew_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v_a_26281__boxed_3129_; lean_object* v_res_3130_; 
v_a_26281__boxed_3129_ = lean_unbox(v_a_3120_);
v_res_3130_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3118_, v_rootNew_3119_, v_a_26281__boxed_3129_, v_a_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v_lhs_3118_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(lean_object* v_lhs_3131_, lean_object* v_rootNew_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_rootNew_3132_, v_a_3137_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; lean_object* v___x_3149_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = lean_box(0);
lean_inc_ref(v_lhs_3131_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v_lhs_3131_);
v___x_3148_ = lean_unbox(v_a_3145_);
lean_dec(v_a_3145_);
v___x_3149_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3131_, v_rootNew_3132_, v___x_3148_, v___x_3147_, v_a_3133_, v_a_3137_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
lean_dec_ref(v_lhs_3131_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3163_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3163_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3163_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v_fst_3154_; 
v_fst_3154_ = lean_ctor_get(v_a_3150_, 0);
lean_inc(v_fst_3154_);
lean_dec(v_a_3150_);
if (lean_obj_tag(v_fst_3154_) == 0)
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3155_ = lean_box(0);
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 0, v___x_3155_);
v___x_3157_ = v___x_3152_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
else
{
lean_object* v_val_3159_; lean_object* v___x_3161_; 
v_val_3159_ = lean_ctor_get(v_fst_3154_, 0);
lean_inc(v_val_3159_);
lean_dec_ref_known(v_fst_3154_, 1);
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 0, v_val_3159_);
v___x_3161_ = v___x_3152_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_val_3159_);
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
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
v_a_3164_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3149_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3149_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
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
lean_dec_ref(v_rootNew_3132_);
lean_dec_ref(v_lhs_3131_);
v_a_3172_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3144_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3144_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots___boxed(lean_object* v_lhs_3180_, lean_object* v_rootNew_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3180_, v_rootNew_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec_ref(v_a_3186_);
lean_dec(v_a_3185_);
lean_dec_ref(v_a_3184_);
lean_dec(v_a_3183_);
lean_dec(v_a_3182_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(lean_object* v___x_3194_, lean_object* v_00_u03b2_3195_, lean_object* v_x_3196_, lean_object* v_x_3197_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___redArg(v___x_3194_, v_x_3196_, v_x_3197_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0___boxed(lean_object* v___x_3199_, lean_object* v_00_u03b2_3200_, lean_object* v_x_3201_, lean_object* v_x_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0(v___x_3199_, v_00_u03b2_3200_, v_x_3201_, v_x_3202_);
lean_dec_ref(v_x_3201_);
lean_dec_ref(v___x_3199_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(lean_object* v___x_3204_, lean_object* v_00_u03b2_3205_, lean_object* v_x_3206_, lean_object* v_x_3207_, lean_object* v_x_3208_){
_start:
{
lean_object* v___x_3209_; 
v___x_3209_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___redArg(v___x_3204_, v_x_3206_, v_x_3207_, v_x_3208_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1___boxed(lean_object* v___x_3210_, lean_object* v_00_u03b2_3211_, lean_object* v_x_3212_, lean_object* v_x_3213_, lean_object* v_x_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1(v___x_3210_, v_00_u03b2_3211_, v_x_3212_, v_x_3213_, v_x_3214_);
lean_dec_ref(v___x_3210_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(lean_object* v_lhs_3216_, lean_object* v_rootNew_3217_, uint8_t v_a_3218_, lean_object* v_inst_3219_, lean_object* v_a_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg(v_lhs_3216_, v_rootNew_3217_, v_a_3218_, v_a_3220_, v___y_3221_, v___y_3225_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___boxed(lean_object* v_lhs_3233_, lean_object* v_rootNew_3234_, lean_object* v_a_3235_, lean_object* v_inst_3236_, lean_object* v_a_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v_a_26640__boxed_3249_; lean_object* v_res_3250_; 
v_a_26640__boxed_3249_ = lean_unbox(v_a_3235_);
v_res_3250_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2(v_lhs_3233_, v_rootNew_3234_, v_a_26640__boxed_3249_, v_inst_3236_, v_a_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v_lhs_3233_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(lean_object* v___x_3251_, lean_object* v_00_u03b2_3252_, lean_object* v_x_3253_, size_t v_x_3254_, lean_object* v_x_3255_){
_start:
{
lean_object* v___x_3256_; 
lean_inc_ref(v_x_3253_);
v___x_3256_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___redArg(v___x_3251_, v_x_3253_, v_x_3254_, v_x_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0___boxed(lean_object* v___x_3257_, lean_object* v_00_u03b2_3258_, lean_object* v_x_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_){
_start:
{
size_t v_x_26683__boxed_3262_; lean_object* v_res_3263_; 
v_x_26683__boxed_3262_ = lean_unbox_usize(v_x_3260_);
lean_dec(v_x_3260_);
v_res_3263_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0(v___x_3257_, v_00_u03b2_3258_, v_x_3259_, v_x_26683__boxed_3262_, v_x_3261_);
lean_dec_ref(v_x_3259_);
lean_dec_ref(v___x_3257_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(lean_object* v___x_3264_, lean_object* v_00_u03b2_3265_, lean_object* v_x_3266_, size_t v_x_3267_, size_t v_x_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___redArg(v___x_3264_, v_x_3266_, v_x_3267_, v_x_3268_, v_x_3269_, v_x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2___boxed(lean_object* v___x_3272_, lean_object* v_00_u03b2_3273_, lean_object* v_x_3274_, lean_object* v_x_3275_, lean_object* v_x_3276_, lean_object* v_x_3277_, lean_object* v_x_3278_){
_start:
{
size_t v_x_26697__boxed_3279_; size_t v_x_26698__boxed_3280_; lean_object* v_res_3281_; 
v_x_26697__boxed_3279_ = lean_unbox_usize(v_x_3275_);
lean_dec(v_x_3275_);
v_x_26698__boxed_3280_ = lean_unbox_usize(v_x_3276_);
lean_dec(v_x_3276_);
v_res_3281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2(v___x_3272_, v_00_u03b2_3273_, v_x_3274_, v_x_26697__boxed_3279_, v_x_26698__boxed_3280_, v_x_3277_, v_x_3278_);
lean_dec_ref(v___x_3272_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(lean_object* v___x_3282_, lean_object* v_00_u03b2_3283_, lean_object* v_keys_3284_, lean_object* v_vals_3285_, lean_object* v_heq_3286_, lean_object* v_i_3287_, lean_object* v_k_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___redArg(v___x_3282_, v_keys_3284_, v_vals_3285_, v_i_3287_, v_k_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1___boxed(lean_object* v___x_3290_, lean_object* v_00_u03b2_3291_, lean_object* v_keys_3292_, lean_object* v_vals_3293_, lean_object* v_heq_3294_, lean_object* v_i_3295_, lean_object* v_k_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__0_spec__0_spec__1(v___x_3290_, v_00_u03b2_3291_, v_keys_3292_, v_vals_3293_, v_heq_3294_, v_i_3295_, v_k_3296_);
lean_dec_ref(v_vals_3293_);
lean_dec_ref(v_keys_3292_);
lean_dec_ref(v___x_3290_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(lean_object* v___x_3298_, lean_object* v_00_u03b2_3299_, lean_object* v_n_3300_, lean_object* v_k_3301_, lean_object* v_v_3302_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___redArg(v___x_3298_, v_n_3300_, v_k_3301_, v_v_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4___boxed(lean_object* v___x_3304_, lean_object* v_00_u03b2_3305_, lean_object* v_n_3306_, lean_object* v_k_3307_, lean_object* v_v_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4(v___x_3304_, v_00_u03b2_3305_, v_n_3306_, v_k_3307_, v_v_3308_);
lean_dec_ref(v___x_3304_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(lean_object* v___x_3310_, lean_object* v_00_u03b2_3311_, size_t v_depth_3312_, lean_object* v_keys_3313_, lean_object* v_vals_3314_, lean_object* v_heq_3315_, lean_object* v_i_3316_, lean_object* v_entries_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___redArg(v___x_3310_, v_depth_3312_, v_keys_3313_, v_vals_3314_, v_i_3316_, v_entries_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5___boxed(lean_object* v___x_3319_, lean_object* v_00_u03b2_3320_, lean_object* v_depth_3321_, lean_object* v_keys_3322_, lean_object* v_vals_3323_, lean_object* v_heq_3324_, lean_object* v_i_3325_, lean_object* v_entries_3326_){
_start:
{
size_t v_depth_boxed_3327_; lean_object* v_res_3328_; 
v_depth_boxed_3327_ = lean_unbox_usize(v_depth_3321_);
lean_dec(v_depth_3321_);
v_res_3328_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__5(v___x_3319_, v_00_u03b2_3320_, v_depth_boxed_3327_, v_keys_3322_, v_vals_3323_, v_heq_3324_, v_i_3325_, v_entries_3326_);
lean_dec_ref(v_vals_3323_);
lean_dec_ref(v_keys_3322_);
lean_dec_ref(v___x_3319_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(lean_object* v___x_3329_, lean_object* v_00_u03b2_3330_, lean_object* v_x_3331_, lean_object* v_x_3332_, lean_object* v_x_3333_, lean_object* v_x_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___redArg(v___x_3329_, v_x_3331_, v_x_3332_, v_x_3333_, v_x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v___x_3336_, lean_object* v_00_u03b2_3337_, lean_object* v_x_3338_, lean_object* v_x_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__1_spec__2_spec__4_spec__6(v___x_3336_, v_00_u03b2_3337_, v_x_3338_, v_x_3339_, v_x_3340_, v_x_3341_);
lean_dec_ref(v___x_3336_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(lean_object* v_as_x27_3343_, lean_object* v_b_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
if (lean_obj_tag(v_as_x27_3343_) == 0)
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v_b_3344_);
return v___x_3356_;
}
else
{
lean_object* v_head_3357_; lean_object* v_tail_3358_; lean_object* v___x_3359_; 
v_head_3357_ = lean_ctor_get(v_as_x27_3343_, 0);
v_tail_3358_ = lean_ctor_get(v_as_x27_3343_, 1);
lean_inc(v_head_3357_);
v___x_3359_ = l_Lean_Meta_Grind_propagateUp(v_head_3357_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v___x_3360_; 
lean_dec_ref_known(v___x_3359_, 1);
v___x_3360_ = lean_box(0);
v_as_x27_3343_ = v_tail_3358_;
v_b_3344_ = v___x_3360_;
goto _start;
}
else
{
return v___x_3359_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg___boxed(lean_object* v_as_x27_3362_, lean_object* v_b_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3362_, v_b_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec(v_as_x27_3362_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(lean_object* v_as_x27_3376_, lean_object* v_b_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
if (lean_obj_tag(v_as_x27_3376_) == 0)
{
lean_object* v___x_3389_; 
v___x_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3389_, 0, v_b_3377_);
return v___x_3389_;
}
else
{
lean_object* v_head_3390_; lean_object* v_tail_3391_; lean_object* v___x_3392_; 
v_head_3390_ = lean_ctor_get(v_as_x27_3376_, 0);
v_tail_3391_ = lean_ctor_get(v_as_x27_3376_, 1);
lean_inc(v_head_3390_);
v___x_3392_ = l_Lean_Meta_Grind_propagateDown(v_head_3390_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v___x_3393_; 
lean_dec_ref_known(v___x_3392_, 1);
v___x_3393_ = lean_box(0);
v_as_x27_3376_ = v_tail_3391_;
v_b_3377_ = v___x_3393_;
goto _start;
}
else
{
return v___x_3392_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg___boxed(lean_object* v_as_x27_3395_, lean_object* v_b_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3395_, v_b_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec(v_as_x27_3395_);
return v_res_3408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1(void){
_start:
{
lean_object* v_cls_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_cls_3412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_3413_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_3414_ = l_Lean_Name_append(v___x_3413_, v_cls_3412_);
return v___x_3414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__2));
v___x_3417_ = l_Lean_stringToMessageData(v___x_3416_);
return v___x_3417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__4));
v___x_3420_ = l_Lean_stringToMessageData(v___x_3419_);
return v___x_3420_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__6));
v___x_3423_ = l_Lean_stringToMessageData(v___x_3422_);
return v___x_3423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__8));
v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(lean_object* v_proof_3427_, uint8_t v_isHEq_3428_, lean_object* v_lhs_3429_, lean_object* v_rhs_3430_, lean_object* v_lhsNode_3431_, lean_object* v_rhsNode_3432_, lean_object* v_lhsRoot_3433_, lean_object* v_rhsRoot_3434_, uint8_t v_flipped_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_){
_start:
{
lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; uint8_t v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; uint8_t v___y_3525_; uint8_t v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; uint8_t v___y_3533_; lean_object* v___y_3534_; uint8_t v___y_3535_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; uint8_t v___y_3571_; uint8_t v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; uint8_t v___y_3590_; lean_object* v___y_3591_; uint8_t v___y_3592_; uint8_t v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; uint8_t v___y_3601_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; uint8_t v___y_3607_; uint8_t v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v_options_3685_; lean_object* v_inheritedTraceOptions_3686_; uint8_t v_hasTrace_3687_; lean_object* v_cls_3688_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v_fns_u2082_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v_fns_u2081_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; 
v_options_3685_ = lean_ctor_get(v_a_3444_, 2);
v_inheritedTraceOptions_3686_ = lean_ctor_get(v_a_3444_, 13);
v_hasTrace_3687_ = lean_ctor_get_uint8(v_options_3685_, sizeof(void*)*1);
v_cls_3688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
if (v_hasTrace_3687_ == 0)
{
v___y_3807_ = v_a_3436_;
v___y_3808_ = v_a_3437_;
v___y_3809_ = v_a_3438_;
v___y_3810_ = v_a_3439_;
v___y_3811_ = v_a_3440_;
v___y_3812_ = v_a_3441_;
v___y_3813_ = v_a_3442_;
v___y_3814_ = v_a_3443_;
v___y_3815_ = v_a_3444_;
v___y_3816_ = v_a_3445_;
goto v___jp_3806_;
}
else
{
lean_object* v___x_3887_; uint8_t v___x_3888_; 
v___x_3887_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3888_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3686_, v_options_3685_, v___x_3887_);
if (v___x_3888_ == 0)
{
v___y_3807_ = v_a_3436_;
v___y_3808_ = v_a_3437_;
v___y_3809_ = v_a_3438_;
v___y_3810_ = v_a_3439_;
v___y_3811_ = v_a_3440_;
v___y_3812_ = v_a_3441_;
v___y_3813_ = v_a_3442_;
v___y_3814_ = v_a_3443_;
v___y_3815_ = v_a_3444_;
v___y_3816_ = v_a_3445_;
goto v___jp_3806_;
}
else
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_Meta_Grind_updateLastTag(v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v___x_3890_; 
lean_dec_ref_known(v___x_3889_, 1);
lean_inc_ref(v_lhs_3429_);
v___x_3890_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3429_, v_a_3436_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3892_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
lean_inc_ref(v_rhs_3430_);
v___x_3892_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_3430_, v_a_3436_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
v___x_3894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__7);
v___x_3895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
lean_ctor_set(v___x_3895_, 1, v_a_3891_);
v___x_3896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__9);
v___x_3897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3895_);
lean_ctor_set(v___x_3897_, 1, v___x_3896_);
v___x_3898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
lean_ctor_set(v___x_3898_, 1, v_a_3893_);
v___x_3899_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3688_, v___x_3898_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_dec_ref_known(v___x_3899_, 1);
v___y_3807_ = v_a_3436_;
v___y_3808_ = v_a_3437_;
v___y_3809_ = v_a_3438_;
v___y_3810_ = v_a_3439_;
v___y_3811_ = v_a_3440_;
v___y_3812_ = v_a_3441_;
v___y_3813_ = v_a_3442_;
v___y_3814_ = v_a_3443_;
v___y_3815_ = v_a_3444_;
v___y_3816_ = v_a_3445_;
goto v___jp_3806_;
}
else
{
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhsNode_3431_);
lean_dec_ref(v_rhs_3430_);
lean_dec_ref(v_lhs_3429_);
lean_dec_ref(v_proof_3427_);
return v___x_3899_;
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec(v_a_3891_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhsNode_3431_);
lean_dec_ref(v_rhs_3430_);
lean_dec_ref(v_lhs_3429_);
lean_dec_ref(v_proof_3427_);
v_a_3900_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3892_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3892_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhsNode_3431_);
lean_dec_ref(v_rhs_3430_);
lean_dec_ref(v_lhs_3429_);
lean_dec_ref(v_proof_3427_);
v_a_3908_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3890_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3890_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhsNode_3431_);
lean_dec_ref(v_rhs_3430_);
lean_dec_ref(v_lhs_3429_);
lean_dec_ref(v_proof_3427_);
return v___x_3889_;
}
}
}
v___jp_3447_:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3454_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3490_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3490_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3490_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_unbox(v_a_3465_);
lean_dec(v_a_3465_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
lean_del_object(v___x_3467_);
v___x_3470_ = l_Lean_Meta_Grind_ParentSet_elems(v___y_3449_);
lean_dec(v___y_3449_);
v___x_3471_ = lean_box(0);
v___x_3472_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v___x_3470_, v___x_3471_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___x_3470_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v___x_3473_; 
lean_dec_ref_known(v___x_3472_, 1);
v___x_3473_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v___y_3448_, v___x_3471_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3474_; 
lean_dec_ref_known(v___x_3473_, 1);
v___x_3474_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_propagateUnitConstFuns(v___y_3451_, v___y_3452_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec_ref(v___y_3452_);
lean_dec_ref(v___y_3451_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v___x_3475_; 
lean_dec_ref_known(v___x_3474_, 1);
v___x_3475_ = l_Lean_Meta_Grind_PendingSolverPropagations_propagate(v___y_3450_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3484_; 
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v___x_3475_, 0);
lean_dec(v_unused_3485_);
v___x_3477_ = v___x_3475_;
v_isShared_3478_ = v_isSharedCheck_3484_;
goto v_resetjp_3476_;
}
else
{
lean_dec(v___x_3475_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3484_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
uint8_t v___x_3479_; 
v___x_3479_ = l_Lean_Expr_isTrue(v___y_3453_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3481_; 
lean_dec(v___y_3448_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3471_);
v___x_3481_ = v___x_3477_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3471_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
else
{
lean_object* v___x_3483_; 
lean_del_object(v___x_3477_);
v___x_3483_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_checkDelayedThmInsts(v___y_3448_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3448_);
return v___x_3483_;
}
}
}
else
{
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3448_);
return v___x_3475_;
}
}
else
{
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3450_);
lean_dec(v___y_3448_);
return v___x_3474_;
}
}
else
{
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec(v___y_3448_);
return v___x_3473_;
}
}
else
{
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec(v___y_3448_);
return v___x_3472_;
}
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec(v___y_3448_);
v___x_3486_ = lean_box(0);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3486_);
v___x_3488_ = v___x_3467_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec(v___y_3448_);
v_a_3491_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3464_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3464_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
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
v___jp_3499_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_inc_ref(v___y_3512_);
v___x_3536_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v___x_3536_, 0, v___y_3512_);
lean_ctor_set(v___x_3536_, 1, v___y_3518_);
lean_ctor_set(v___x_3536_, 2, v___y_3532_);
lean_ctor_set(v___x_3536_, 3, v___y_3507_);
lean_ctor_set(v___x_3536_, 4, v___y_3522_);
lean_ctor_set(v___x_3536_, 5, v___y_3500_);
lean_ctor_set(v___x_3536_, 6, v___y_3514_);
lean_ctor_set(v___x_3536_, 7, v___y_3502_);
lean_ctor_set(v___x_3536_, 8, v___y_3513_);
lean_ctor_set(v___x_3536_, 9, v___y_3520_);
lean_ctor_set(v___x_3536_, 10, v___y_3501_);
lean_ctor_set(v___x_3536_, 11, v___y_3519_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12, v___y_3517_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12 + 1, v___y_3523_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12 + 2, v___y_3525_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12 + 3, v___y_3533_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12 + 4, v___y_3535_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*12 + 5, v___y_3526_);
lean_inc_ref(v___y_3510_);
v___x_3537_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3510_, v___x_3536_, v___y_3516_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v___x_3538_; 
lean_dec_ref_known(v___x_3537_, 1);
lean_inc_ref(v___y_3534_);
v___x_3538_ = l_Lean_Meta_Grind_propagateBeta(v___y_3534_, v___y_3511_, v___y_3516_, v___y_3515_, v___y_3531_, v___y_3506_, v___y_3521_, v___y_3509_, v___y_3528_, v___y_3505_, v___y_3527_, v___y_3524_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v___x_3539_; 
lean_dec_ref_known(v___x_3538_, 1);
lean_inc_ref(v___y_3508_);
v___x_3539_ = l_Lean_Meta_Grind_propagateBeta(v___y_3508_, v___y_3530_, v___y_3516_, v___y_3515_, v___y_3531_, v___y_3506_, v___y_3521_, v___y_3509_, v___y_3528_, v___y_3505_, v___y_3527_, v___y_3524_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v___x_3540_; 
lean_dec_ref_known(v___x_3539_, 1);
v___x_3540_ = l_Lean_Meta_Grind_Solvers_mergeTerms___redArg(v_rhsRoot_3434_, v_lhsRoot_3433_, v___y_3516_, v___y_3528_, v___y_3505_, v___y_3527_, v___y_3524_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3542_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3540_, 1);
v___x_3542_ = l_Lean_Meta_Grind_resetParentsOf___redArg(v___y_3503_, v___y_3516_);
lean_dec_ref(v___y_3503_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v___x_3543_; 
lean_dec_ref_known(v___x_3542_, 1);
lean_inc_ref(v___y_3510_);
v___x_3543_ = l_Lean_Meta_Grind_copyParentsTo(v___y_3504_, v___y_3510_, v___y_3516_, v___y_3515_, v___y_3531_, v___y_3506_, v___y_3521_, v___y_3509_, v___y_3528_, v___y_3505_, v___y_3527_, v___y_3524_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v___x_3544_; 
lean_dec_ref_known(v___x_3543_, 1);
v___x_3544_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_3516_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; uint8_t v___x_3546_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v___x_3546_ = lean_unbox(v_a_3545_);
lean_dec(v_a_3545_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; 
v___x_3547_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_updateMT(v___y_3512_, v___y_3516_, v___y_3515_, v___y_3531_, v___y_3506_, v___y_3521_, v___y_3509_, v___y_3528_, v___y_3505_, v___y_3527_, v___y_3524_);
lean_dec_ref(v___y_3512_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_dec_ref_known(v___x_3547_, 1);
v___y_3448_ = v___y_3529_;
v___y_3449_ = v___y_3504_;
v___y_3450_ = v_a_3541_;
v___y_3451_ = v___y_3534_;
v___y_3452_ = v___y_3508_;
v___y_3453_ = v___y_3510_;
v___y_3454_ = v___y_3516_;
v___y_3455_ = v___y_3515_;
v___y_3456_ = v___y_3531_;
v___y_3457_ = v___y_3506_;
v___y_3458_ = v___y_3521_;
v___y_3459_ = v___y_3509_;
v___y_3460_ = v___y_3528_;
v___y_3461_ = v___y_3505_;
v___y_3462_ = v___y_3527_;
v___y_3463_ = v___y_3524_;
goto v___jp_3447_;
}
else
{
lean_dec(v_a_3541_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3510_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3504_);
return v___x_3547_;
}
}
else
{
lean_dec_ref(v___y_3512_);
v___y_3448_ = v___y_3529_;
v___y_3449_ = v___y_3504_;
v___y_3450_ = v_a_3541_;
v___y_3451_ = v___y_3534_;
v___y_3452_ = v___y_3508_;
v___y_3453_ = v___y_3510_;
v___y_3454_ = v___y_3516_;
v___y_3455_ = v___y_3515_;
v___y_3456_ = v___y_3531_;
v___y_3457_ = v___y_3506_;
v___y_3458_ = v___y_3521_;
v___y_3459_ = v___y_3509_;
v___y_3460_ = v___y_3528_;
v___y_3461_ = v___y_3505_;
v___y_3462_ = v___y_3527_;
v___y_3463_ = v___y_3524_;
goto v___jp_3447_;
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec(v_a_3541_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3510_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3504_);
v_a_3548_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3544_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3544_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_dec(v_a_3541_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3510_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3504_);
return v___x_3543_;
}
}
else
{
lean_dec(v_a_3541_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3510_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3504_);
return v___x_3542_;
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3510_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
v_a_3556_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3540_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3540_);
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
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3510_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
return v___x_3539_;
}
}
else
{
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3510_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
return v___x_3538_;
}
}
else
{
lean_dec_ref(v___y_3534_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
return v___x_3537_;
}
}
v___jp_3564_:
{
if (v_isHEq_3428_ == 0)
{
if (v___y_3571_ == 0)
{
v___y_3500_ = v___y_3566_;
v___y_3501_ = v___y_3565_;
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3568_;
v___y_3505_ = v___y_3570_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3574_;
v___y_3508_ = v___y_3575_;
v___y_3509_ = v___y_3578_;
v___y_3510_ = v___y_3577_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3583_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3585_;
v___y_3519_ = v___y_3586_;
v___y_3520_ = v___y_3587_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3589_;
v___y_3523_ = v___y_3590_;
v___y_3524_ = v___y_3591_;
v___y_3525_ = v___y_3593_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3595_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3596_;
v___y_3530_ = v___y_3598_;
v___y_3531_ = v___y_3597_;
v___y_3532_ = v___y_3599_;
v___y_3533_ = v___y_3601_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3572_;
goto v___jp_3499_;
}
else
{
v___y_3500_ = v___y_3566_;
v___y_3501_ = v___y_3565_;
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3568_;
v___y_3505_ = v___y_3570_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3574_;
v___y_3508_ = v___y_3575_;
v___y_3509_ = v___y_3578_;
v___y_3510_ = v___y_3577_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3583_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3585_;
v___y_3519_ = v___y_3586_;
v___y_3520_ = v___y_3587_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3589_;
v___y_3523_ = v___y_3590_;
v___y_3524_ = v___y_3591_;
v___y_3525_ = v___y_3593_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3595_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3596_;
v___y_3530_ = v___y_3598_;
v___y_3531_ = v___y_3597_;
v___y_3532_ = v___y_3599_;
v___y_3533_ = v___y_3601_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v___y_3571_;
goto v___jp_3499_;
}
}
else
{
v___y_3500_ = v___y_3566_;
v___y_3501_ = v___y_3565_;
v___y_3502_ = v___y_3567_;
v___y_3503_ = v___y_3569_;
v___y_3504_ = v___y_3568_;
v___y_3505_ = v___y_3570_;
v___y_3506_ = v___y_3573_;
v___y_3507_ = v___y_3574_;
v___y_3508_ = v___y_3575_;
v___y_3509_ = v___y_3578_;
v___y_3510_ = v___y_3577_;
v___y_3511_ = v___y_3576_;
v___y_3512_ = v___y_3579_;
v___y_3513_ = v___y_3580_;
v___y_3514_ = v___y_3581_;
v___y_3515_ = v___y_3582_;
v___y_3516_ = v___y_3583_;
v___y_3517_ = v___y_3584_;
v___y_3518_ = v___y_3585_;
v___y_3519_ = v___y_3586_;
v___y_3520_ = v___y_3587_;
v___y_3521_ = v___y_3588_;
v___y_3522_ = v___y_3589_;
v___y_3523_ = v___y_3590_;
v___y_3524_ = v___y_3591_;
v___y_3525_ = v___y_3593_;
v___y_3526_ = v___y_3592_;
v___y_3527_ = v___y_3595_;
v___y_3528_ = v___y_3594_;
v___y_3529_ = v___y_3596_;
v___y_3530_ = v___y_3598_;
v___y_3531_ = v___y_3597_;
v___y_3532_ = v___y_3599_;
v___y_3533_ = v___y_3601_;
v___y_3534_ = v___y_3600_;
v___y_3535_ = v_isHEq_3428_;
goto v___jp_3499_;
}
}
v___jp_3602_:
{
lean_object* v___x_3625_; 
v___x_3625_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_reinsertParents(v___y_3605_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
lean_dec_ref_known(v___x_3625_, 1);
v___x_3626_ = lean_st_ref_get(v___y_3615_);
v___x_3627_ = lean_st_ref_get(v___y_3615_);
lean_inc_ref(v___y_3604_);
v___x_3628_ = l_Lean_Meta_Grind_Goal_getENode(v___x_3627_, v___y_3604_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___x_3627_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v_self_3630_; lean_object* v_root_3631_; lean_object* v_congr_3632_; lean_object* v_target_x3f_3633_; lean_object* v_proof_x3f_3634_; uint8_t v_flipped_3635_; lean_object* v_size_3636_; uint8_t v_interpreted_3637_; uint8_t v_ctor_3638_; uint8_t v_hasLambdas_3639_; uint8_t v_heqProofs_3640_; lean_object* v_idx_3641_; lean_object* v_generation_3642_; lean_object* v_mt_3643_; lean_object* v_sTerms_3644_; uint8_t v_funCC_3645_; lean_object* v_ematchDiagSource_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3675_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3628_, 1);
v_self_3630_ = lean_ctor_get(v_a_3629_, 0);
v_root_3631_ = lean_ctor_get(v_a_3629_, 2);
v_congr_3632_ = lean_ctor_get(v_a_3629_, 3);
v_target_x3f_3633_ = lean_ctor_get(v_a_3629_, 4);
v_proof_x3f_3634_ = lean_ctor_get(v_a_3629_, 5);
v_flipped_3635_ = lean_ctor_get_uint8(v_a_3629_, sizeof(void*)*12);
v_size_3636_ = lean_ctor_get(v_a_3629_, 6);
v_interpreted_3637_ = lean_ctor_get_uint8(v_a_3629_, sizeof(void*)*12 + 1);
v_ctor_3638_ = lean_ctor_get_uint8(v_a_3629_, sizeof(void*)*12 + 2);
v_hasLambdas_3639_ = lean_ctor_get_uint8(v_a_3629_, sizeof(void*)*12 + 3);
v_heqProofs_3640_ = lean_ctor_get_uint8(v_a_3629_, sizeof(void*)*12 + 4);
v_idx_3641_ = lean_ctor_get(v_a_3629_, 7);
v_generation_3642_ = lean_ctor_get(v_a_3629_, 8);
v_mt_3643_ = lean_ctor_get(v_a_3629_, 9);
v_sTerms_3644_ = lean_ctor_get(v_a_3629_, 10);
v_funCC_3645_ = lean_ctor_get_uint8(v_a_3629_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3646_ = lean_ctor_get(v_a_3629_, 11);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_a_3629_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v_a_3629_, 1);
lean_dec(v_unused_3676_);
v___x_3648_ = v_a_3629_;
v_isShared_3649_ = v_isSharedCheck_3675_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_ematchDiagSource_3646_);
lean_inc(v_sTerms_3644_);
lean_inc(v_mt_3643_);
lean_inc(v_generation_3642_);
lean_inc(v_idx_3641_);
lean_inc(v_size_3636_);
lean_inc(v_proof_x3f_3634_);
lean_inc(v_target_x3f_3633_);
lean_inc(v_congr_3632_);
lean_inc(v_root_3631_);
lean_inc(v_self_3630_);
lean_dec(v_a_3629_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3675_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v_self_3650_; lean_object* v_next_3651_; lean_object* v_root_3652_; lean_object* v_congr_3653_; lean_object* v_target_x3f_3654_; lean_object* v_proof_x3f_3655_; uint8_t v_flipped_3656_; lean_object* v_size_3657_; uint8_t v_interpreted_3658_; uint8_t v_ctor_3659_; uint8_t v_hasLambdas_3660_; uint8_t v_heqProofs_3661_; lean_object* v_idx_3662_; lean_object* v_generation_3663_; lean_object* v_mt_3664_; lean_object* v_sTerms_3665_; uint8_t v_funCC_3666_; lean_object* v_ematchDiagSource_3667_; lean_object* v___x_3669_; 
v_self_3650_ = lean_ctor_get(v_rhsRoot_3434_, 0);
v_next_3651_ = lean_ctor_get(v_rhsRoot_3434_, 1);
v_root_3652_ = lean_ctor_get(v_rhsRoot_3434_, 2);
v_congr_3653_ = lean_ctor_get(v_rhsRoot_3434_, 3);
v_target_x3f_3654_ = lean_ctor_get(v_rhsRoot_3434_, 4);
v_proof_x3f_3655_ = lean_ctor_get(v_rhsRoot_3434_, 5);
v_flipped_3656_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12);
v_size_3657_ = lean_ctor_get(v_rhsRoot_3434_, 6);
v_interpreted_3658_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12 + 1);
v_ctor_3659_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12 + 2);
v_hasLambdas_3660_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12 + 3);
v_heqProofs_3661_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12 + 4);
v_idx_3662_ = lean_ctor_get(v_rhsRoot_3434_, 7);
v_generation_3663_ = lean_ctor_get(v_rhsRoot_3434_, 8);
v_mt_3664_ = lean_ctor_get(v_rhsRoot_3434_, 9);
v_sTerms_3665_ = lean_ctor_get(v_rhsRoot_3434_, 10);
v_funCC_3666_ = lean_ctor_get_uint8(v_rhsRoot_3434_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3667_ = lean_ctor_get(v_rhsRoot_3434_, 11);
lean_inc_ref(v_next_3651_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 1, v_next_3651_);
v___x_3669_ = v___x_3648_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_self_3630_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_next_3651_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_root_3631_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_congr_3632_);
lean_ctor_set(v_reuseFailAlloc_3674_, 4, v_target_x3f_3633_);
lean_ctor_set(v_reuseFailAlloc_3674_, 5, v_proof_x3f_3634_);
lean_ctor_set(v_reuseFailAlloc_3674_, 6, v_size_3636_);
lean_ctor_set(v_reuseFailAlloc_3674_, 7, v_idx_3641_);
lean_ctor_set(v_reuseFailAlloc_3674_, 8, v_generation_3642_);
lean_ctor_set(v_reuseFailAlloc_3674_, 9, v_mt_3643_);
lean_ctor_set(v_reuseFailAlloc_3674_, 10, v_sTerms_3644_);
lean_ctor_set(v_reuseFailAlloc_3674_, 11, v_ematchDiagSource_3646_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12, v_flipped_3635_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12 + 1, v_interpreted_3637_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12 + 2, v_ctor_3638_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12 + 3, v_hasLambdas_3639_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12 + 4, v_heqProofs_3640_);
lean_ctor_set_uint8(v_reuseFailAlloc_3674_, sizeof(void*)*12 + 5, v_funCC_3645_);
v___x_3669_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Lean_Meta_Grind_setENode___redArg(v___y_3609_, v___x_3669_, v___y_3615_);
if (lean_obj_tag(v___x_3670_) == 0)
{
uint8_t v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_dec_ref_known(v___x_3670_, 1);
v___x_3671_ = 0;
v___x_3672_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3626_, v_lhs_3429_, v___x_3671_);
lean_dec(v___x_3626_);
v___x_3673_ = lean_nat_add(v_size_3657_, v___y_3603_);
lean_dec(v___y_3603_);
if (v_hasLambdas_3660_ == 0)
{
lean_inc_ref(v_root_3652_);
lean_inc(v_target_x3f_3654_);
lean_inc(v_mt_3664_);
lean_inc(v_ematchDiagSource_3667_);
lean_inc(v_generation_3663_);
lean_inc_ref(v_self_3650_);
lean_inc_ref(v_congr_3653_);
lean_inc(v_idx_3662_);
lean_inc(v_proof_x3f_3655_);
lean_inc(v_sTerms_3665_);
v___y_3565_ = v_sTerms_3665_;
v___y_3566_ = v_proof_x3f_3655_;
v___y_3567_ = v_idx_3662_;
v___y_3568_ = v___y_3605_;
v___y_3569_ = v___y_3604_;
v___y_3570_ = v___y_3622_;
v___y_3571_ = v_heqProofs_3661_;
v___y_3572_ = v___y_3608_;
v___y_3573_ = v___y_3618_;
v___y_3574_ = v_congr_3653_;
v___y_3575_ = v___y_3612_;
v___y_3576_ = v___y_3614_;
v___y_3577_ = v___y_3613_;
v___y_3578_ = v___y_3620_;
v___y_3579_ = v_self_3650_;
v___y_3580_ = v_generation_3663_;
v___y_3581_ = v___x_3673_;
v___y_3582_ = v___y_3616_;
v___y_3583_ = v___y_3615_;
v___y_3584_ = v_flipped_3656_;
v___y_3585_ = v___y_3610_;
v___y_3586_ = v_ematchDiagSource_3667_;
v___y_3587_ = v_mt_3664_;
v___y_3588_ = v___y_3619_;
v___y_3589_ = v_target_x3f_3654_;
v___y_3590_ = v_interpreted_3658_;
v___y_3591_ = v___y_3624_;
v___y_3592_ = v_funCC_3666_;
v___y_3593_ = v_ctor_3659_;
v___y_3594_ = v___y_3621_;
v___y_3595_ = v___y_3623_;
v___y_3596_ = v___x_3672_;
v___y_3597_ = v___y_3617_;
v___y_3598_ = v___y_3606_;
v___y_3599_ = v_root_3652_;
v___y_3600_ = v___y_3611_;
v___y_3601_ = v___y_3607_;
goto v___jp_3564_;
}
else
{
lean_inc_ref(v_root_3652_);
lean_inc(v_target_x3f_3654_);
lean_inc(v_mt_3664_);
lean_inc(v_ematchDiagSource_3667_);
lean_inc(v_generation_3663_);
lean_inc_ref(v_self_3650_);
lean_inc_ref(v_congr_3653_);
lean_inc(v_idx_3662_);
lean_inc(v_proof_x3f_3655_);
lean_inc(v_sTerms_3665_);
v___y_3565_ = v_sTerms_3665_;
v___y_3566_ = v_proof_x3f_3655_;
v___y_3567_ = v_idx_3662_;
v___y_3568_ = v___y_3605_;
v___y_3569_ = v___y_3604_;
v___y_3570_ = v___y_3622_;
v___y_3571_ = v_heqProofs_3661_;
v___y_3572_ = v___y_3608_;
v___y_3573_ = v___y_3618_;
v___y_3574_ = v_congr_3653_;
v___y_3575_ = v___y_3612_;
v___y_3576_ = v___y_3614_;
v___y_3577_ = v___y_3613_;
v___y_3578_ = v___y_3620_;
v___y_3579_ = v_self_3650_;
v___y_3580_ = v_generation_3663_;
v___y_3581_ = v___x_3673_;
v___y_3582_ = v___y_3616_;
v___y_3583_ = v___y_3615_;
v___y_3584_ = v_flipped_3656_;
v___y_3585_ = v___y_3610_;
v___y_3586_ = v_ematchDiagSource_3667_;
v___y_3587_ = v_mt_3664_;
v___y_3588_ = v___y_3619_;
v___y_3589_ = v_target_x3f_3654_;
v___y_3590_ = v_interpreted_3658_;
v___y_3591_ = v___y_3624_;
v___y_3592_ = v_funCC_3666_;
v___y_3593_ = v_ctor_3659_;
v___y_3594_ = v___y_3621_;
v___y_3595_ = v___y_3623_;
v___y_3596_ = v___x_3672_;
v___y_3597_ = v___y_3617_;
v___y_3598_ = v___y_3606_;
v___y_3599_ = v_root_3652_;
v___y_3600_ = v___y_3611_;
v___y_3601_ = v_hasLambdas_3660_;
goto v___jp_3564_;
}
}
else
{
lean_dec(v___x_3626_);
lean_dec_ref(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec(v___x_3626_);
lean_dec_ref(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
v_a_3677_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3628_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3628_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_dec_ref(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
return v___x_3625_;
}
}
v___jp_3689_:
{
lean_object* v_self_3705_; lean_object* v_next_3706_; lean_object* v_size_3707_; uint8_t v_hasLambdas_3708_; uint8_t v_heqProofs_3709_; lean_object* v___x_3710_; 
v_self_3705_ = lean_ctor_get(v_lhsRoot_3433_, 0);
v_next_3706_ = lean_ctor_get(v_lhsRoot_3433_, 1);
v_size_3707_ = lean_ctor_get(v_lhsRoot_3433_, 6);
v_hasLambdas_3708_ = lean_ctor_get_uint8(v_lhsRoot_3433_, sizeof(void*)*12 + 3);
v_heqProofs_3709_ = lean_ctor_get_uint8(v_lhsRoot_3433_, sizeof(void*)*12 + 4);
v___x_3710_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents(v_self_3705_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v_root_3712_; lean_object* v___x_3713_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
v_root_3712_ = lean_ctor_get(v_rhsNode_3432_, 2);
lean_inc_ref_n(v_root_3712_, 2);
lean_dec_ref(v_rhsNode_3432_);
lean_inc_ref(v_lhs_3429_);
v___x_3713_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots(v_lhs_3429_, v_root_3712_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_options_3714_; uint8_t v_hasTrace_3715_; 
lean_dec_ref_known(v___x_3713_, 1);
v_options_3714_ = lean_ctor_get(v___y_3703_, 2);
v_hasTrace_3715_ = lean_ctor_get_uint8(v_options_3714_, sizeof(void*)*1);
if (v_hasTrace_3715_ == 0)
{
lean_inc_ref(v_next_3706_);
lean_inc_ref(v_self_3705_);
lean_inc(v_size_3707_);
v___y_3603_ = v_size_3707_;
v___y_3604_ = v_self_3705_;
v___y_3605_ = v_a_3711_;
v___y_3606_ = v_fns_u2082_3694_;
v___y_3607_ = v_hasLambdas_3708_;
v___y_3608_ = v_heqProofs_3709_;
v___y_3609_ = v___y_3690_;
v___y_3610_ = v_next_3706_;
v___y_3611_ = v___y_3691_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v_root_3712_;
v___y_3614_ = v___y_3693_;
v___y_3615_ = v___y_3695_;
v___y_3616_ = v___y_3696_;
v___y_3617_ = v___y_3697_;
v___y_3618_ = v___y_3698_;
v___y_3619_ = v___y_3699_;
v___y_3620_ = v___y_3700_;
v___y_3621_ = v___y_3701_;
v___y_3622_ = v___y_3702_;
v___y_3623_ = v___y_3703_;
v___y_3624_ = v___y_3704_;
goto v___jp_3602_;
}
else
{
lean_object* v_inheritedTraceOptions_3716_; lean_object* v___x_3717_; uint8_t v___x_3718_; 
v_inheritedTraceOptions_3716_ = lean_ctor_get(v___y_3703_, 13);
v___x_3717_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_3718_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3716_, v_options_3714_, v___x_3717_);
if (v___x_3718_ == 0)
{
lean_inc_ref(v_next_3706_);
lean_inc_ref(v_self_3705_);
lean_inc(v_size_3707_);
v___y_3603_ = v_size_3707_;
v___y_3604_ = v_self_3705_;
v___y_3605_ = v_a_3711_;
v___y_3606_ = v_fns_u2082_3694_;
v___y_3607_ = v_hasLambdas_3708_;
v___y_3608_ = v_heqProofs_3709_;
v___y_3609_ = v___y_3690_;
v___y_3610_ = v_next_3706_;
v___y_3611_ = v___y_3691_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v_root_3712_;
v___y_3614_ = v___y_3693_;
v___y_3615_ = v___y_3695_;
v___y_3616_ = v___y_3696_;
v___y_3617_ = v___y_3697_;
v___y_3618_ = v___y_3698_;
v___y_3619_ = v___y_3699_;
v___y_3620_ = v___y_3700_;
v___y_3621_ = v___y_3701_;
v___y_3622_ = v___y_3702_;
v___y_3623_ = v___y_3703_;
v___y_3624_ = v___y_3704_;
goto v___jp_3602_;
}
else
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lean_Meta_Grind_updateLastTag(v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v___x_3720_; 
lean_dec_ref_known(v___x_3719_, 1);
lean_inc_ref(v_lhs_3429_);
v___x_3720_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_3429_, v___y_3695_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3722_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
lean_inc_ref(v_root_3712_);
v___x_3722_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_root_3712_, v___y_3695_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
v___x_3724_ = lean_st_ref_get(v___y_3695_);
lean_inc_ref(v_lhs_3429_);
v___x_3725_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_3724_, v_lhs_3429_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec(v___x_3724_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v___x_3727_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v___x_3725_, 1);
v___x_3727_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_a_3726_, v___y_3695_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___x_3729_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__3);
v___x_3730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_a_3721_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
lean_ctor_set(v___x_3731_, 1, v_a_3723_);
v___x_3732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__5);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
lean_ctor_set(v___x_3734_, 1, v_a_3728_);
v___x_3735_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v_cls_3688_, v___x_3734_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_dec_ref_known(v___x_3735_, 1);
lean_inc_ref(v_next_3706_);
lean_inc_ref(v_self_3705_);
lean_inc(v_size_3707_);
v___y_3603_ = v_size_3707_;
v___y_3604_ = v_self_3705_;
v___y_3605_ = v_a_3711_;
v___y_3606_ = v_fns_u2082_3694_;
v___y_3607_ = v_hasLambdas_3708_;
v___y_3608_ = v_heqProofs_3709_;
v___y_3609_ = v___y_3690_;
v___y_3610_ = v_next_3706_;
v___y_3611_ = v___y_3691_;
v___y_3612_ = v___y_3692_;
v___y_3613_ = v_root_3712_;
v___y_3614_ = v___y_3693_;
v___y_3615_ = v___y_3695_;
v___y_3616_ = v___y_3696_;
v___y_3617_ = v___y_3697_;
v___y_3618_ = v___y_3698_;
v___y_3619_ = v___y_3699_;
v___y_3620_ = v___y_3700_;
v___y_3621_ = v___y_3701_;
v___y_3622_ = v___y_3702_;
v___y_3623_ = v___y_3703_;
v___y_3624_ = v___y_3704_;
goto v___jp_3602_;
}
else
{
lean_dec_ref(v_root_3712_);
lean_dec(v_a_3711_);
lean_dec_ref(v_fns_u2082_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
return v___x_3735_;
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v_a_3723_);
lean_dec(v_a_3721_);
lean_dec_ref(v_root_3712_);
lean_dec(v_a_3711_);
lean_dec_ref(v_fns_u2082_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
v_a_3736_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3727_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3727_);
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
lean_dec(v_a_3723_);
lean_dec(v_a_3721_);
lean_dec_ref(v_root_3712_);
lean_dec(v_a_3711_);
lean_dec_ref(v_fns_u2082_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
v_a_3744_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3725_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3725_);
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
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec(v_a_3721_);
lean_dec_ref(v_root_3712_);
lean_dec(v_a_3711_);
lean_dec_ref(v_fns_u2082_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
v_a_3752_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3722_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3722_);
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
lean_dec(v_a_3711_);
lean_dec_ref(v_fns_u2082_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
v_a_3760_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3720_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3720_);
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
lean_dec(v_a_3711_);
lean_dec_ref(v_fns_u2082_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
return v___x_3719_;
}
}
}
}
else
{
lean_dec_ref(v_root_3712_);
lean_dec(v_a_3711_);
lean_dec_ref(v_fns_u2082_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_lhs_3429_);
return v___x_3713_;
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v_fns_u2082_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
v_a_3768_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3710_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3710_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
v___jp_3776_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; 
v___x_3791_ = lean_array_get_size(v___y_3779_);
v___x_3792_ = lean_unsigned_to_nat(0u);
v___x_3793_ = lean_nat_dec_eq(v___x_3791_, v___x_3792_);
if (v___x_3793_ == 0)
{
lean_object* v_self_3794_; lean_object* v___x_3795_; 
v_self_3794_ = lean_ctor_get(v_lhsRoot_3433_, 0);
lean_inc_ref(v_self_3794_);
v___x_3795_ = l_Lean_Meta_Grind_getFnRoots(v_self_3794_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3795_, 1);
v___y_3690_ = v___y_3777_;
v___y_3691_ = v___y_3778_;
v___y_3692_ = v___y_3779_;
v___y_3693_ = v_fns_u2081_3780_;
v_fns_u2082_3694_ = v_a_3796_;
v___y_3695_ = v___y_3781_;
v___y_3696_ = v___y_3782_;
v___y_3697_ = v___y_3783_;
v___y_3698_ = v___y_3784_;
v___y_3699_ = v___y_3785_;
v___y_3700_ = v___y_3786_;
v___y_3701_ = v___y_3787_;
v___y_3702_ = v___y_3788_;
v___y_3703_ = v___y_3789_;
v___y_3704_ = v___y_3790_;
goto v___jp_3689_;
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec_ref(v_fns_u2081_3780_);
lean_dec_ref(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
v_a_3797_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3795_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3795_);
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
lean_object* v___x_3805_; 
v___x_3805_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3690_ = v___y_3777_;
v___y_3691_ = v___y_3778_;
v___y_3692_ = v___y_3779_;
v___y_3693_ = v_fns_u2081_3780_;
v_fns_u2082_3694_ = v___x_3805_;
v___y_3695_ = v___y_3781_;
v___y_3696_ = v___y_3782_;
v___y_3697_ = v___y_3783_;
v___y_3698_ = v___y_3784_;
v___y_3699_ = v___y_3785_;
v___y_3700_ = v___y_3786_;
v___y_3701_ = v___y_3787_;
v___y_3702_ = v___y_3788_;
v___y_3703_ = v___y_3789_;
v___y_3704_ = v___y_3790_;
goto v___jp_3689_;
}
}
v___jp_3806_:
{
lean_object* v___x_3817_; 
lean_inc_ref(v_lhs_3429_);
v___x_3817_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_invertTrans___redArg(v_lhs_3429_, v___y_3807_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3885_; 
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; 
v_unused_3886_ = lean_ctor_get(v___x_3817_, 0);
lean_dec(v_unused_3886_);
v___x_3819_ = v___x_3817_;
v_isShared_3820_ = v_isSharedCheck_3885_;
goto v_resetjp_3818_;
}
else
{
lean_dec(v___x_3817_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3885_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v_self_3821_; lean_object* v_next_3822_; lean_object* v_root_3823_; lean_object* v_congr_3824_; lean_object* v_size_3825_; uint8_t v_interpreted_3826_; uint8_t v_ctor_3827_; uint8_t v_hasLambdas_3828_; uint8_t v_heqProofs_3829_; lean_object* v_idx_3830_; lean_object* v_generation_3831_; lean_object* v_mt_3832_; lean_object* v_sTerms_3833_; uint8_t v_funCC_3834_; lean_object* v_ematchDiagSource_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3882_; 
v_self_3821_ = lean_ctor_get(v_lhsNode_3431_, 0);
v_next_3822_ = lean_ctor_get(v_lhsNode_3431_, 1);
v_root_3823_ = lean_ctor_get(v_lhsNode_3431_, 2);
v_congr_3824_ = lean_ctor_get(v_lhsNode_3431_, 3);
v_size_3825_ = lean_ctor_get(v_lhsNode_3431_, 6);
v_interpreted_3826_ = lean_ctor_get_uint8(v_lhsNode_3431_, sizeof(void*)*12 + 1);
v_ctor_3827_ = lean_ctor_get_uint8(v_lhsNode_3431_, sizeof(void*)*12 + 2);
v_hasLambdas_3828_ = lean_ctor_get_uint8(v_lhsNode_3431_, sizeof(void*)*12 + 3);
v_heqProofs_3829_ = lean_ctor_get_uint8(v_lhsNode_3431_, sizeof(void*)*12 + 4);
v_idx_3830_ = lean_ctor_get(v_lhsNode_3431_, 7);
v_generation_3831_ = lean_ctor_get(v_lhsNode_3431_, 8);
v_mt_3832_ = lean_ctor_get(v_lhsNode_3431_, 9);
v_sTerms_3833_ = lean_ctor_get(v_lhsNode_3431_, 10);
v_funCC_3834_ = lean_ctor_get_uint8(v_lhsNode_3431_, sizeof(void*)*12 + 5);
v_ematchDiagSource_3835_ = lean_ctor_get(v_lhsNode_3431_, 11);
v_isSharedCheck_3882_ = !lean_is_exclusive(v_lhsNode_3431_);
if (v_isSharedCheck_3882_ == 0)
{
lean_object* v_unused_3883_; lean_object* v_unused_3884_; 
v_unused_3883_ = lean_ctor_get(v_lhsNode_3431_, 5);
lean_dec(v_unused_3883_);
v_unused_3884_ = lean_ctor_get(v_lhsNode_3431_, 4);
lean_dec(v_unused_3884_);
v___x_3837_ = v_lhsNode_3431_;
v_isShared_3838_ = v_isSharedCheck_3882_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_ematchDiagSource_3835_);
lean_inc(v_sTerms_3833_);
lean_inc(v_mt_3832_);
lean_inc(v_generation_3831_);
lean_inc(v_idx_3830_);
lean_inc(v_size_3825_);
lean_inc(v_congr_3824_);
lean_inc(v_root_3823_);
lean_inc(v_next_3822_);
lean_inc(v_self_3821_);
lean_dec(v_lhsNode_3431_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3882_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3820_ == 0)
{
lean_ctor_set_tag(v___x_3819_, 1);
lean_ctor_set(v___x_3819_, 0, v_rhs_3430_);
v___x_3840_ = v___x_3819_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_rhs_3430_);
v___x_3840_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3841_, 0, v_proof_3427_);
lean_inc_ref(v_root_3823_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 5, v___x_3841_);
lean_ctor_set(v___x_3837_, 4, v___x_3840_);
v___x_3843_ = v___x_3837_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 12, 6);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_self_3821_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v_next_3822_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v_root_3823_);
lean_ctor_set(v_reuseFailAlloc_3880_, 3, v_congr_3824_);
lean_ctor_set(v_reuseFailAlloc_3880_, 4, v___x_3840_);
lean_ctor_set(v_reuseFailAlloc_3880_, 5, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3880_, 6, v_size_3825_);
lean_ctor_set(v_reuseFailAlloc_3880_, 7, v_idx_3830_);
lean_ctor_set(v_reuseFailAlloc_3880_, 8, v_generation_3831_);
lean_ctor_set(v_reuseFailAlloc_3880_, 9, v_mt_3832_);
lean_ctor_set(v_reuseFailAlloc_3880_, 10, v_sTerms_3833_);
lean_ctor_set(v_reuseFailAlloc_3880_, 11, v_ematchDiagSource_3835_);
lean_ctor_set_uint8(v_reuseFailAlloc_3880_, sizeof(void*)*12 + 1, v_interpreted_3826_);
lean_ctor_set_uint8(v_reuseFailAlloc_3880_, sizeof(void*)*12 + 2, v_ctor_3827_);
lean_ctor_set_uint8(v_reuseFailAlloc_3880_, sizeof(void*)*12 + 3, v_hasLambdas_3828_);
lean_ctor_set_uint8(v_reuseFailAlloc_3880_, sizeof(void*)*12 + 4, v_heqProofs_3829_);
lean_ctor_set_uint8(v_reuseFailAlloc_3880_, sizeof(void*)*12 + 5, v_funCC_3834_);
v___x_3843_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3844_; 
lean_ctor_set_uint8(v___x_3843_, sizeof(void*)*12, v_flipped_3435_);
lean_inc_ref(v_lhs_3429_);
v___x_3844_ = l_Lean_Meta_Grind_setENode___redArg(v_lhs_3429_, v___x_3843_, v___y_3807_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v___x_3845_; 
lean_dec_ref_known(v___x_3844_, 1);
v___x_3845_ = l_Lean_Meta_Grind_getEqcLambdas(v_lhsRoot_3433_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3847_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v___x_3847_ = l_Lean_Meta_Grind_getEqcLambdas(v_rhsRoot_3434_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v___x_3849_ = lean_array_get_size(v_a_3846_);
v___x_3850_ = lean_unsigned_to_nat(0u);
v___x_3851_ = lean_nat_dec_eq(v___x_3849_, v___x_3850_);
if (v___x_3851_ == 0)
{
lean_object* v_self_3852_; lean_object* v___x_3853_; 
v_self_3852_ = lean_ctor_get(v_rhsRoot_3434_, 0);
lean_inc_ref(v_self_3852_);
v___x_3853_ = l_Lean_Meta_Grind_getFnRoots(v_self_3852_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
v___y_3777_ = v_root_3823_;
v___y_3778_ = v_a_3846_;
v___y_3779_ = v_a_3848_;
v_fns_u2081_3780_ = v_a_3854_;
v___y_3781_ = v___y_3807_;
v___y_3782_ = v___y_3808_;
v___y_3783_ = v___y_3809_;
v___y_3784_ = v___y_3810_;
v___y_3785_ = v___y_3811_;
v___y_3786_ = v___y_3812_;
v___y_3787_ = v___y_3813_;
v___y_3788_ = v___y_3814_;
v___y_3789_ = v___y_3815_;
v___y_3790_ = v___y_3816_;
goto v___jp_3776_;
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v_a_3848_);
lean_dec(v_a_3846_);
lean_dec_ref(v_root_3823_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
v_a_3855_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3853_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3853_);
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
lean_object* v___x_3863_; 
v___x_3863_ = ((lean_object*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Meta_Grind_propagateBeta_spec__1_spec__1___redArg___closed__0));
v___y_3777_ = v_root_3823_;
v___y_3778_ = v_a_3846_;
v___y_3779_ = v_a_3848_;
v_fns_u2081_3780_ = v___x_3863_;
v___y_3781_ = v___y_3807_;
v___y_3782_ = v___y_3808_;
v___y_3783_ = v___y_3809_;
v___y_3784_ = v___y_3810_;
v___y_3785_ = v___y_3811_;
v___y_3786_ = v___y_3812_;
v___y_3787_ = v___y_3813_;
v___y_3788_ = v___y_3814_;
v___y_3789_ = v___y_3815_;
v___y_3790_ = v___y_3816_;
goto v___jp_3776_;
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec(v_a_3846_);
lean_dec_ref(v_root_3823_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
v_a_3864_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3847_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3847_);
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
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec_ref(v_root_3823_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
v_a_3872_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3845_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3845_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
else
{
lean_dec_ref(v_root_3823_);
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhs_3429_);
return v___x_3844_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_rhsRoot_3434_);
lean_dec_ref(v_lhsRoot_3433_);
lean_dec_ref(v_rhsNode_3432_);
lean_dec_ref(v_lhsNode_3431_);
lean_dec_ref(v_rhs_3430_);
lean_dec_ref(v_lhs_3429_);
lean_dec_ref(v_proof_3427_);
return v___x_3817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___boxed(lean_object** _args){
lean_object* v_proof_3916_ = _args[0];
lean_object* v_isHEq_3917_ = _args[1];
lean_object* v_lhs_3918_ = _args[2];
lean_object* v_rhs_3919_ = _args[3];
lean_object* v_lhsNode_3920_ = _args[4];
lean_object* v_rhsNode_3921_ = _args[5];
lean_object* v_lhsRoot_3922_ = _args[6];
lean_object* v_rhsRoot_3923_ = _args[7];
lean_object* v_flipped_3924_ = _args[8];
lean_object* v_a_3925_ = _args[9];
lean_object* v_a_3926_ = _args[10];
lean_object* v_a_3927_ = _args[11];
lean_object* v_a_3928_ = _args[12];
lean_object* v_a_3929_ = _args[13];
lean_object* v_a_3930_ = _args[14];
lean_object* v_a_3931_ = _args[15];
lean_object* v_a_3932_ = _args[16];
lean_object* v_a_3933_ = _args[17];
lean_object* v_a_3934_ = _args[18];
lean_object* v_a_3935_ = _args[19];
_start:
{
uint8_t v_isHEq_boxed_3936_; uint8_t v_flipped_boxed_3937_; lean_object* v_res_3938_; 
v_isHEq_boxed_3936_ = lean_unbox(v_isHEq_3917_);
v_flipped_boxed_3937_ = lean_unbox(v_flipped_3924_);
v_res_3938_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_3916_, v_isHEq_boxed_3936_, v_lhs_3918_, v_rhs_3919_, v_lhsNode_3920_, v_rhsNode_3921_, v_lhsRoot_3922_, v_rhsRoot_3923_, v_flipped_boxed_3937_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec(v_a_3925_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(lean_object* v_as_3939_, lean_object* v_as_x27_3940_, lean_object* v_b_3941_, lean_object* v_a_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___redArg(v_as_x27_3940_, v_b_3941_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0___boxed(lean_object* v_as_3955_, lean_object* v_as_x27_3956_, lean_object* v_b_3957_, lean_object* v_a_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__0(v_as_3955_, v_as_x27_3956_, v_b_3957_, v_a_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec(v_as_x27_3956_);
lean_dec(v_as_3955_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(lean_object* v_as_3971_, lean_object* v_as_x27_3972_, lean_object* v_b_3973_, lean_object* v_a_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___redArg(v_as_x27_3972_, v_b_3973_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1___boxed(lean_object* v_as_3987_, lean_object* v_as_x27_3988_, lean_object* v_b_3989_, lean_object* v_a_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go_spec__1(v_as_3987_, v_as_x27_3988_, v_b_3989_, v_a_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec(v_as_x27_3988_);
lean_dec(v_as_3987_);
return v_res_4002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1(void){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__0));
v___x_4005_ = l_Lean_stringToMessageData(v___x_4004_);
return v___x_4005_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4(void){
_start:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4011_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_4012_ = l_Lean_Name_append(v___x_4011_, v___x_4010_);
return v___x_4012_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6(void){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__5));
v___x_4015_ = l_Lean_stringToMessageData(v___x_4014_);
return v___x_4015_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8(void){
_start:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__7));
v___x_4018_ = l_Lean_stringToMessageData(v___x_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(lean_object* v_lhs_4019_, lean_object* v_rhs_4020_, lean_object* v_proof_4021_, uint8_t v_isHEq_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = lean_st_ref_get(v_a_4023_);
lean_inc_ref(v_lhs_4019_);
v___x_4038_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4037_, v_lhs_4019_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
lean_dec(v___x_4037_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref_known(v___x_4038_, 1);
v___x_4040_ = lean_st_ref_get(v_a_4023_);
lean_inc_ref(v_rhs_4020_);
v___x_4041_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4040_, v_rhs_4020_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
lean_dec(v___x_4040_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v_root_4043_; lean_object* v_root_4044_; size_t v___x_4045_; size_t v___x_4046_; uint8_t v___x_4047_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___x_4041_, 1);
v_root_4043_ = lean_ctor_get(v_a_4039_, 2);
v_root_4044_ = lean_ctor_get(v_a_4042_, 2);
v___x_4045_ = lean_ptr_addr(v_root_4043_);
v___x_4046_ = lean_ptr_addr(v_root_4044_);
v___x_4047_ = lean_usize_dec_eq(v___x_4045_, v___x_4046_);
if (v___x_4047_ == 0)
{
lean_object* v_options_4048_; lean_object* v_inheritedTraceOptions_4049_; uint8_t v_hasTrace_4050_; uint8_t v___x_4051_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4088_; lean_object* v___y_4089_; uint8_t v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4116_; lean_object* v___y_4117_; uint8_t v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4146_; uint8_t v___y_4147_; lean_object* v___y_4148_; uint8_t v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; uint8_t v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; uint8_t v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; uint8_t v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; uint8_t v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; uint8_t v___y_4194_; lean_object* v___y_4195_; lean_object* v_size_4196_; uint8_t v_interpreted_4197_; uint8_t v_ctor_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4207_; uint8_t v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; uint8_t v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; uint8_t v_ctor_4224_; lean_object* v___y_4225_; uint8_t v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4236_; lean_object* v___y_4237_; uint8_t v_valueInconsistency_4238_; uint8_t v_trueEqFalse_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; uint8_t v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; 
v_options_4048_ = lean_ctor_get(v_a_4031_, 2);
v_inheritedTraceOptions_4049_ = lean_ctor_get(v_a_4031_, 13);
v_hasTrace_4050_ = lean_ctor_get_uint8(v_options_4048_, sizeof(void*)*1);
v___x_4051_ = 1;
if (v_hasTrace_4050_ == 0)
{
v___y_4296_ = v_a_4023_;
v___y_4297_ = v_a_4024_;
v___y_4298_ = v_a_4025_;
v___y_4299_ = v_a_4026_;
v___y_4300_ = v_a_4027_;
v___y_4301_ = v_a_4028_;
v___y_4302_ = v_a_4029_;
v___y_4303_ = v_a_4030_;
v___y_4304_ = v_a_4031_;
v___y_4305_ = v_a_4032_;
goto v___jp_4295_;
}
else
{
lean_object* v___x_4339_; lean_object* v_____do__lift_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___x_4354_; uint8_t v___x_4355_; 
v___x_4339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__3));
v___x_4354_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__4);
v___x_4355_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4049_, v_options_4048_, v___x_4354_);
if (v___x_4355_ == 0)
{
v___y_4296_ = v_a_4023_;
v___y_4297_ = v_a_4024_;
v___y_4298_ = v_a_4025_;
v___y_4299_ = v_a_4026_;
v___y_4300_ = v_a_4027_;
v___y_4301_ = v_a_4028_;
v___y_4302_ = v_a_4029_;
v___y_4303_ = v_a_4030_;
v___y_4304_ = v_a_4031_;
v___y_4305_ = v_a_4032_;
goto v___jp_4295_;
}
else
{
lean_object* v___x_4356_; 
v___x_4356_ = l_Lean_Meta_Grind_updateLastTag(v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_dec_ref_known(v___x_4356_, 1);
if (v_isHEq_4022_ == 0)
{
lean_object* v___x_4357_; 
lean_inc_ref(v_rhs_4020_);
lean_inc_ref(v_lhs_4019_);
v___x_4357_ = l_Lean_Meta_mkEq(v_lhs_4019_, v_rhs_4020_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v_____do__lift_4341_ = v_a_4358_;
v___y_4342_ = v_a_4023_;
v___y_4343_ = v_a_4024_;
v___y_4344_ = v_a_4025_;
v___y_4345_ = v_a_4026_;
v___y_4346_ = v_a_4027_;
v___y_4347_ = v_a_4028_;
v___y_4348_ = v_a_4029_;
v___y_4349_ = v_a_4030_;
v___y_4350_ = v_a_4031_;
v___y_4351_ = v_a_4032_;
goto v___jp_4340_;
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
lean_dec(v_a_4042_);
lean_dec(v_a_4039_);
lean_dec_ref(v_proof_4021_);
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
v_a_4359_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4357_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4357_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
else
{
lean_object* v___x_4367_; 
lean_inc_ref(v_rhs_4020_);
lean_inc_ref(v_lhs_4019_);
v___x_4367_ = l_Lean_Meta_mkHEq(v_lhs_4019_, v_rhs_4020_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4368_);
lean_dec_ref_known(v___x_4367_, 1);
v_____do__lift_4341_ = v_a_4368_;
v___y_4342_ = v_a_4023_;
v___y_4343_ = v_a_4024_;
v___y_4344_ = v_a_4025_;
v___y_4345_ = v_a_4026_;
v___y_4346_ = v_a_4027_;
v___y_4347_ = v_a_4028_;
v___y_4348_ = v_a_4029_;
v___y_4349_ = v_a_4030_;
v___y_4350_ = v_a_4031_;
v___y_4351_ = v_a_4032_;
goto v___jp_4340_;
}
else
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4376_; 
lean_dec(v_a_4042_);
lean_dec(v_a_4039_);
lean_dec_ref(v_proof_4021_);
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
v_a_4369_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4371_ = v___x_4367_;
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4367_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4372_ == 0)
{
v___x_4374_ = v___x_4371_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4369_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
}
}
else
{
lean_dec(v_a_4042_);
lean_dec(v_a_4039_);
lean_dec_ref(v_proof_4021_);
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
return v___x_4356_;
}
}
v___jp_4340_:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4352_ = l_Lean_MessageData_ofExpr(v_____do__lift_4341_);
v___x_4353_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4339_, v___x_4352_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_dec_ref_known(v___x_4353_, 1);
v___y_4296_ = v___y_4342_;
v___y_4297_ = v___y_4343_;
v___y_4298_ = v___y_4344_;
v___y_4299_ = v___y_4345_;
v___y_4300_ = v___y_4346_;
v___y_4301_ = v___y_4347_;
v___y_4302_ = v___y_4348_;
v___y_4303_ = v___y_4349_;
v___y_4304_ = v___y_4350_;
v___y_4305_ = v___y_4351_;
goto v___jp_4295_;
}
else
{
lean_dec(v_a_4042_);
lean_dec(v_a_4039_);
lean_dec_ref(v_proof_4021_);
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
return v___x_4353_;
}
}
}
v___jp_4052_:
{
lean_object* v_options_4063_; uint8_t v_hasTrace_4064_; 
v_options_4063_ = lean_ctor_get(v___y_4061_, 2);
v_hasTrace_4064_ = lean_ctor_get_uint8(v_options_4063_, sizeof(void*)*1);
if (v_hasTrace_4064_ == 0)
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Lean_Meta_Grind_checkInvariants(v___x_4047_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
return v___x_4065_;
}
else
{
lean_object* v_inheritedTraceOptions_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; uint8_t v___x_4069_; 
v_inheritedTraceOptions_4066_ = lean_ctor_get(v___y_4061_, 13);
v___x_4067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4068_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4069_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4066_, v_options_4063_, v___x_4068_);
if (v___x_4069_ == 0)
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Lean_Meta_Grind_checkInvariants(v___x_4047_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
return v___x_4070_;
}
else
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_Meta_Grind_updateLastTag(v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
lean_dec_ref_known(v___x_4071_, 1);
v___x_4072_ = lean_st_ref_get(v___y_4053_);
v___x_4073_ = l_Lean_Meta_Grind_Goal_ppState(v___x_4072_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
lean_dec(v___x_4072_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4073_, 1);
v___x_4075_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__1);
v___x_4076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
lean_ctor_set(v___x_4076_, 1, v_a_4074_);
v___x_4077_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4067_, v___x_4076_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v___x_4078_; 
lean_dec_ref_known(v___x_4077_, 1);
v___x_4078_ = l_Lean_Meta_Grind_checkInvariants(v___x_4047_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
return v___x_4078_;
}
else
{
return v___x_4077_;
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
v_a_4079_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4073_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4073_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
else
{
return v___x_4071_;
}
}
}
}
v___jp_4087_:
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Lean_Meta_Grind_isInconsistent___redArg(v___y_4091_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; uint8_t v___x_4103_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4101_, 1);
v___x_4103_ = lean_unbox(v_a_4102_);
lean_dec(v_a_4102_);
if (v___x_4103_ == 0)
{
if (v___y_4090_ == 0)
{
lean_dec_ref(v___y_4089_);
lean_dec_ref(v___y_4088_);
v___y_4053_ = v___y_4091_;
v___y_4054_ = v___y_4092_;
v___y_4055_ = v___y_4093_;
v___y_4056_ = v___y_4094_;
v___y_4057_ = v___y_4095_;
v___y_4058_ = v___y_4096_;
v___y_4059_ = v___y_4097_;
v___y_4060_ = v___y_4098_;
v___y_4061_ = v___y_4099_;
v___y_4062_ = v___y_4100_;
goto v___jp_4052_;
}
else
{
lean_object* v_self_4104_; lean_object* v_self_4105_; lean_object* v___x_4106_; 
v_self_4104_ = lean_ctor_get(v___y_4088_, 0);
lean_inc_ref(v_self_4104_);
lean_dec_ref(v___y_4088_);
v_self_4105_ = lean_ctor_get(v___y_4089_, 0);
lean_inc_ref(v_self_4105_);
lean_dec_ref(v___y_4089_);
v___x_4106_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithValuesEq(v_self_4104_, v_self_4105_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_dec_ref_known(v___x_4106_, 1);
v___y_4053_ = v___y_4091_;
v___y_4054_ = v___y_4092_;
v___y_4055_ = v___y_4093_;
v___y_4056_ = v___y_4094_;
v___y_4057_ = v___y_4095_;
v___y_4058_ = v___y_4096_;
v___y_4059_ = v___y_4097_;
v___y_4060_ = v___y_4098_;
v___y_4061_ = v___y_4099_;
v___y_4062_ = v___y_4100_;
goto v___jp_4052_;
}
else
{
return v___x_4106_;
}
}
}
else
{
lean_dec_ref(v___y_4089_);
lean_dec_ref(v___y_4088_);
v___y_4053_ = v___y_4091_;
v___y_4054_ = v___y_4092_;
v___y_4055_ = v___y_4093_;
v___y_4056_ = v___y_4094_;
v___y_4057_ = v___y_4095_;
v___y_4058_ = v___y_4096_;
v___y_4059_ = v___y_4097_;
v___y_4060_ = v___y_4098_;
v___y_4061_ = v___y_4099_;
v___y_4062_ = v___y_4100_;
goto v___jp_4052_;
}
}
else
{
lean_object* v_a_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4114_; 
lean_dec_ref(v___y_4089_);
lean_dec_ref(v___y_4088_);
v_a_4107_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4109_ = v___x_4101_;
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_a_4107_);
lean_dec(v___x_4101_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4114_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4112_; 
if (v_isShared_4110_ == 0)
{
v___x_4112_ = v___x_4109_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
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
v_ctor_4132_ = lean_ctor_get_uint8(v___y_4116_, sizeof(void*)*12 + 2);
if (v_ctor_4132_ == 0)
{
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
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
goto v___jp_4087_;
}
else
{
uint8_t v_ctor_4133_; 
v_ctor_4133_ = lean_ctor_get_uint8(v___y_4117_, sizeof(void*)*12 + 2);
if (v_ctor_4133_ == 0)
{
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
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
goto v___jp_4087_;
}
else
{
lean_object* v_self_4134_; lean_object* v_self_4135_; lean_object* v___x_4136_; 
v_self_4134_ = lean_ctor_get(v___y_4116_, 0);
v_self_4135_ = lean_ctor_get(v___y_4117_, 0);
lean_inc_ref(v_self_4135_);
lean_inc_ref(v_self_4134_);
v___x_4136_ = l_Lean_Meta_Grind_propagateCtor(v_self_4134_, v_self_4135_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_dec_ref_known(v___x_4136_, 1);
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
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
goto v___jp_4087_;
}
else
{
lean_dec_ref(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v___x_4136_;
}
}
}
}
else
{
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
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
goto v___jp_4087_;
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec_ref(v___y_4117_);
lean_dec_ref(v___y_4116_);
v_a_4137_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4129_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4129_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
v___jp_4145_:
{
if (v___y_4147_ == 0)
{
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
v___y_4127_ = v___y_4158_;
v___y_4128_ = v___y_4159_;
goto v___jp_4115_;
}
else
{
lean_object* v___x_4160_; 
v___x_4160_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_closeGoalWithTrueEqFalse(v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_dec_ref_known(v___x_4160_, 1);
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
v___y_4127_ = v___y_4158_;
v___y_4128_ = v___y_4159_;
goto v___jp_4115_;
}
else
{
lean_dec_ref(v___y_4148_);
lean_dec_ref(v___y_4146_);
return v___x_4160_;
}
}
}
v___jp_4161_:
{
lean_object* v___x_4176_; 
lean_inc_ref(v___y_4171_);
lean_inc_ref(v___y_4163_);
v___x_4176_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4021_, v_isHEq_4022_, v_rhs_4020_, v_lhs_4019_, v_a_4042_, v_a_4039_, v___y_4163_, v___y_4171_, v___x_4051_, v___y_4167_, v___y_4164_, v___y_4169_, v___y_4165_, v___y_4174_, v___y_4172_, v___y_4166_, v___y_4175_, v___y_4170_, v___y_4168_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_dec_ref_known(v___x_4176_, 1);
v___y_4146_ = v___y_4171_;
v___y_4147_ = v___y_4162_;
v___y_4148_ = v___y_4163_;
v___y_4149_ = v___y_4173_;
v___y_4150_ = v___y_4167_;
v___y_4151_ = v___y_4164_;
v___y_4152_ = v___y_4169_;
v___y_4153_ = v___y_4165_;
v___y_4154_ = v___y_4174_;
v___y_4155_ = v___y_4172_;
v___y_4156_ = v___y_4166_;
v___y_4157_ = v___y_4175_;
v___y_4158_ = v___y_4170_;
v___y_4159_ = v___y_4168_;
goto v___jp_4145_;
}
else
{
lean_dec_ref(v___y_4171_);
lean_dec_ref(v___y_4163_);
return v___x_4176_;
}
}
v___jp_4177_:
{
lean_object* v___x_4192_; 
lean_inc_ref(v___y_4179_);
lean_inc_ref(v___y_4187_);
v___x_4192_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go(v_proof_4021_, v_isHEq_4022_, v_lhs_4019_, v_rhs_4020_, v_a_4039_, v_a_4042_, v___y_4187_, v___y_4179_, v___x_4047_, v___y_4183_, v___y_4180_, v___y_4185_, v___y_4181_, v___y_4190_, v___y_4188_, v___y_4182_, v___y_4191_, v___y_4186_, v___y_4184_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_dec_ref_known(v___x_4192_, 1);
v___y_4146_ = v___y_4187_;
v___y_4147_ = v___y_4178_;
v___y_4148_ = v___y_4179_;
v___y_4149_ = v___y_4189_;
v___y_4150_ = v___y_4183_;
v___y_4151_ = v___y_4180_;
v___y_4152_ = v___y_4185_;
v___y_4153_ = v___y_4181_;
v___y_4154_ = v___y_4190_;
v___y_4155_ = v___y_4188_;
v___y_4156_ = v___y_4182_;
v___y_4157_ = v___y_4191_;
v___y_4158_ = v___y_4186_;
v___y_4159_ = v___y_4184_;
goto v___jp_4145_;
}
else
{
lean_dec_ref(v___y_4187_);
lean_dec_ref(v___y_4179_);
return v___x_4192_;
}
}
v___jp_4193_:
{
lean_object* v_size_4211_; uint8_t v___x_4212_; 
v_size_4211_ = lean_ctor_get(v___y_4206_, 6);
v___x_4212_ = lean_nat_dec_lt(v_size_4196_, v_size_4211_);
lean_dec(v_size_4196_);
if (v___x_4212_ == 0)
{
v___y_4178_ = v___y_4194_;
v___y_4179_ = v___y_4195_;
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
v___y_4190_ = v___y_4210_;
v___y_4191_ = v___y_4209_;
goto v___jp_4177_;
}
else
{
if (v_interpreted_4197_ == 0)
{
if (v_ctor_4198_ == 0)
{
v___y_4162_ = v___y_4194_;
v___y_4163_ = v___y_4195_;
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
v___y_4174_ = v___y_4210_;
v___y_4175_ = v___y_4209_;
goto v___jp_4161_;
}
else
{
v___y_4178_ = v___y_4194_;
v___y_4179_ = v___y_4195_;
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
v___y_4190_ = v___y_4210_;
v___y_4191_ = v___y_4209_;
goto v___jp_4177_;
}
}
else
{
v___y_4178_ = v___y_4194_;
v___y_4179_ = v___y_4195_;
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
v___y_4190_ = v___y_4210_;
v___y_4191_ = v___y_4209_;
goto v___jp_4177_;
}
}
}
v___jp_4213_:
{
if (v_ctor_4224_ == 0)
{
lean_object* v_size_4229_; uint8_t v_interpreted_4230_; uint8_t v_ctor_4231_; 
v_size_4229_ = lean_ctor_get(v___y_4215_, 6);
lean_inc(v_size_4229_);
v_interpreted_4230_ = lean_ctor_get_uint8(v___y_4215_, sizeof(void*)*12 + 1);
v_ctor_4231_ = lean_ctor_get_uint8(v___y_4215_, sizeof(void*)*12 + 2);
v___y_4194_ = v___y_4214_;
v___y_4195_ = v___y_4215_;
v_size_4196_ = v_size_4229_;
v_interpreted_4197_ = v_interpreted_4230_;
v_ctor_4198_ = v_ctor_4231_;
v___y_4199_ = v___y_4216_;
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4219_;
v___y_4203_ = v___y_4220_;
v___y_4204_ = v___y_4221_;
v___y_4205_ = v___y_4222_;
v___y_4206_ = v___y_4223_;
v___y_4207_ = v___y_4225_;
v___y_4208_ = v___y_4226_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4227_;
goto v___jp_4193_;
}
else
{
uint8_t v_ctor_4232_; 
v_ctor_4232_ = lean_ctor_get_uint8(v___y_4215_, sizeof(void*)*12 + 2);
if (v_ctor_4232_ == 0)
{
v___y_4162_ = v___y_4214_;
v___y_4163_ = v___y_4215_;
v___y_4164_ = v___y_4216_;
v___y_4165_ = v___y_4217_;
v___y_4166_ = v___y_4218_;
v___y_4167_ = v___y_4219_;
v___y_4168_ = v___y_4220_;
v___y_4169_ = v___y_4221_;
v___y_4170_ = v___y_4222_;
v___y_4171_ = v___y_4223_;
v___y_4172_ = v___y_4225_;
v___y_4173_ = v___y_4226_;
v___y_4174_ = v___y_4227_;
v___y_4175_ = v___y_4228_;
goto v___jp_4161_;
}
else
{
lean_object* v_size_4233_; uint8_t v_interpreted_4234_; 
v_size_4233_ = lean_ctor_get(v___y_4215_, 6);
lean_inc(v_size_4233_);
v_interpreted_4234_ = lean_ctor_get_uint8(v___y_4215_, sizeof(void*)*12 + 1);
v___y_4194_ = v___y_4214_;
v___y_4195_ = v___y_4215_;
v_size_4196_ = v_size_4233_;
v_interpreted_4197_ = v_interpreted_4234_;
v_ctor_4198_ = v_ctor_4232_;
v___y_4199_ = v___y_4216_;
v___y_4200_ = v___y_4217_;
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4219_;
v___y_4203_ = v___y_4220_;
v___y_4204_ = v___y_4221_;
v___y_4205_ = v___y_4222_;
v___y_4206_ = v___y_4223_;
v___y_4207_ = v___y_4225_;
v___y_4208_ = v___y_4226_;
v___y_4209_ = v___y_4228_;
v___y_4210_ = v___y_4227_;
goto v___jp_4193_;
}
}
}
v___jp_4235_:
{
uint8_t v_interpreted_4250_; 
v_interpreted_4250_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 1);
if (v_interpreted_4250_ == 0)
{
uint8_t v_ctor_4251_; 
v_ctor_4251_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 2);
v___y_4214_ = v_trueEqFalse_4239_;
v___y_4215_ = v___y_4237_;
v___y_4216_ = v___y_4241_;
v___y_4217_ = v___y_4243_;
v___y_4218_ = v___y_4246_;
v___y_4219_ = v___y_4240_;
v___y_4220_ = v___y_4249_;
v___y_4221_ = v___y_4242_;
v___y_4222_ = v___y_4248_;
v___y_4223_ = v___y_4236_;
v_ctor_4224_ = v_ctor_4251_;
v___y_4225_ = v___y_4245_;
v___y_4226_ = v_valueInconsistency_4238_;
v___y_4227_ = v___y_4244_;
v___y_4228_ = v___y_4247_;
goto v___jp_4213_;
}
else
{
uint8_t v_interpreted_4252_; 
v_interpreted_4252_ = lean_ctor_get_uint8(v___y_4237_, sizeof(void*)*12 + 1);
if (v_interpreted_4252_ == 0)
{
v___y_4162_ = v_trueEqFalse_4239_;
v___y_4163_ = v___y_4237_;
v___y_4164_ = v___y_4241_;
v___y_4165_ = v___y_4243_;
v___y_4166_ = v___y_4246_;
v___y_4167_ = v___y_4240_;
v___y_4168_ = v___y_4249_;
v___y_4169_ = v___y_4242_;
v___y_4170_ = v___y_4248_;
v___y_4171_ = v___y_4236_;
v___y_4172_ = v___y_4245_;
v___y_4173_ = v_valueInconsistency_4238_;
v___y_4174_ = v___y_4244_;
v___y_4175_ = v___y_4247_;
goto v___jp_4161_;
}
else
{
uint8_t v_ctor_4253_; 
v_ctor_4253_ = lean_ctor_get_uint8(v___y_4236_, sizeof(void*)*12 + 2);
v___y_4214_ = v_trueEqFalse_4239_;
v___y_4215_ = v___y_4237_;
v___y_4216_ = v___y_4241_;
v___y_4217_ = v___y_4243_;
v___y_4218_ = v___y_4246_;
v___y_4219_ = v___y_4240_;
v___y_4220_ = v___y_4249_;
v___y_4221_ = v___y_4242_;
v___y_4222_ = v___y_4248_;
v___y_4223_ = v___y_4236_;
v_ctor_4224_ = v_ctor_4253_;
v___y_4225_ = v___y_4245_;
v___y_4226_ = v_valueInconsistency_4238_;
v___y_4227_ = v___y_4244_;
v___y_4228_ = v___y_4247_;
goto v___jp_4213_;
}
}
}
v___jp_4254_:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Lean_Meta_Grind_markAsInconsistent___redArg(v___y_4261_, v___y_4260_, v___y_4259_, v___y_4263_, v___y_4264_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_dec_ref_known(v___x_4267_, 1);
v___y_4236_ = v___y_4262_;
v___y_4237_ = v___y_4258_;
v_valueInconsistency_4238_ = v___x_4047_;
v_trueEqFalse_4239_ = v___x_4051_;
v___y_4240_ = v___y_4261_;
v___y_4241_ = v___y_4255_;
v___y_4242_ = v___y_4257_;
v___y_4243_ = v___y_4256_;
v___y_4244_ = v___y_4266_;
v___y_4245_ = v___y_4265_;
v___y_4246_ = v___y_4260_;
v___y_4247_ = v___y_4259_;
v___y_4248_ = v___y_4263_;
v___y_4249_ = v___y_4264_;
goto v___jp_4235_;
}
else
{
lean_dec_ref(v___y_4262_);
lean_dec_ref(v___y_4258_);
lean_dec(v_a_4042_);
lean_dec(v_a_4039_);
lean_dec_ref(v_proof_4021_);
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
return v___x_4267_;
}
}
v___jp_4268_:
{
if (v___y_4275_ == 0)
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Lean_Meta_Grind_hasSameType(v___y_4273_, v___y_4276_, v___y_4277_, v___y_4274_, v___y_4280_, v___y_4281_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v_a_4285_; uint8_t v___x_4286_; 
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
lean_inc(v_a_4285_);
lean_dec_ref_known(v___x_4284_, 1);
v___x_4286_ = lean_unbox(v_a_4285_);
lean_dec(v_a_4285_);
if (v___x_4286_ == 0)
{
v___y_4236_ = v___y_4278_;
v___y_4237_ = v___y_4272_;
v_valueInconsistency_4238_ = v___x_4047_;
v_trueEqFalse_4239_ = v___x_4047_;
v___y_4240_ = v___y_4279_;
v___y_4241_ = v___y_4269_;
v___y_4242_ = v___y_4271_;
v___y_4243_ = v___y_4270_;
v___y_4244_ = v___y_4283_;
v___y_4245_ = v___y_4282_;
v___y_4246_ = v___y_4277_;
v___y_4247_ = v___y_4274_;
v___y_4248_ = v___y_4280_;
v___y_4249_ = v___y_4281_;
goto v___jp_4235_;
}
else
{
v___y_4236_ = v___y_4278_;
v___y_4237_ = v___y_4272_;
v_valueInconsistency_4238_ = v___x_4051_;
v_trueEqFalse_4239_ = v___x_4047_;
v___y_4240_ = v___y_4279_;
v___y_4241_ = v___y_4269_;
v___y_4242_ = v___y_4271_;
v___y_4243_ = v___y_4270_;
v___y_4244_ = v___y_4283_;
v___y_4245_ = v___y_4282_;
v___y_4246_ = v___y_4277_;
v___y_4247_ = v___y_4274_;
v___y_4248_ = v___y_4280_;
v___y_4249_ = v___y_4281_;
goto v___jp_4235_;
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec_ref(v___y_4278_);
lean_dec_ref(v___y_4272_);
lean_dec(v_a_4042_);
lean_dec(v_a_4039_);
lean_dec_ref(v_proof_4021_);
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
v_a_4287_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4284_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4284_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
else
{
lean_dec_ref(v___y_4276_);
lean_dec_ref(v___y_4273_);
v___y_4236_ = v___y_4278_;
v___y_4237_ = v___y_4272_;
v_valueInconsistency_4238_ = v___x_4051_;
v_trueEqFalse_4239_ = v___x_4047_;
v___y_4240_ = v___y_4279_;
v___y_4241_ = v___y_4269_;
v___y_4242_ = v___y_4271_;
v___y_4243_ = v___y_4270_;
v___y_4244_ = v___y_4283_;
v___y_4245_ = v___y_4282_;
v___y_4246_ = v___y_4277_;
v___y_4247_ = v___y_4274_;
v___y_4248_ = v___y_4280_;
v___y_4249_ = v___y_4281_;
goto v___jp_4235_;
}
}
v___jp_4295_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4306_ = lean_st_ref_get(v___y_4296_);
lean_inc_ref(v_root_4043_);
v___x_4307_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4306_, v_root_4043_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
lean_dec(v___x_4306_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4307_, 1);
v___x_4309_ = lean_st_ref_get(v___y_4296_);
lean_inc_ref(v_root_4044_);
v___x_4310_ = l_Lean_Meta_Grind_Goal_getENode(v___x_4309_, v_root_4044_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
lean_dec(v___x_4309_);
if (lean_obj_tag(v___x_4310_) == 0)
{
uint8_t v_interpreted_4311_; 
v_interpreted_4311_ = lean_ctor_get_uint8(v_a_4308_, sizeof(void*)*12 + 1);
if (v_interpreted_4311_ == 0)
{
lean_object* v_a_4312_; uint8_t v_ctor_4313_; 
v_a_4312_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4310_, 1);
v_ctor_4313_ = lean_ctor_get_uint8(v_a_4308_, sizeof(void*)*12 + 2);
v___y_4214_ = v___x_4047_;
v___y_4215_ = v_a_4312_;
v___y_4216_ = v___y_4297_;
v___y_4217_ = v___y_4299_;
v___y_4218_ = v___y_4302_;
v___y_4219_ = v___y_4296_;
v___y_4220_ = v___y_4305_;
v___y_4221_ = v___y_4298_;
v___y_4222_ = v___y_4304_;
v___y_4223_ = v_a_4308_;
v_ctor_4224_ = v_ctor_4313_;
v___y_4225_ = v___y_4301_;
v___y_4226_ = v___x_4047_;
v___y_4227_ = v___y_4300_;
v___y_4228_ = v___y_4303_;
goto v___jp_4213_;
}
else
{
lean_object* v_a_4314_; uint8_t v_interpreted_4315_; 
v_a_4314_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4310_, 1);
v_interpreted_4315_ = lean_ctor_get_uint8(v_a_4314_, sizeof(void*)*12 + 1);
if (v_interpreted_4315_ == 0)
{
v___y_4162_ = v___x_4047_;
v___y_4163_ = v_a_4314_;
v___y_4164_ = v___y_4297_;
v___y_4165_ = v___y_4299_;
v___y_4166_ = v___y_4302_;
v___y_4167_ = v___y_4296_;
v___y_4168_ = v___y_4305_;
v___y_4169_ = v___y_4298_;
v___y_4170_ = v___y_4304_;
v___y_4171_ = v_a_4308_;
v___y_4172_ = v___y_4301_;
v___y_4173_ = v___x_4047_;
v___y_4174_ = v___y_4300_;
v___y_4175_ = v___y_4303_;
goto v___jp_4161_;
}
else
{
lean_object* v_self_4316_; uint8_t v_ctor_4317_; uint8_t v_heqProofs_4318_; lean_object* v_self_4319_; uint8_t v_heqProofs_4320_; uint8_t v___x_4321_; 
v_self_4316_ = lean_ctor_get(v_a_4308_, 0);
v_ctor_4317_ = lean_ctor_get_uint8(v_a_4308_, sizeof(void*)*12 + 2);
v_heqProofs_4318_ = lean_ctor_get_uint8(v_a_4308_, sizeof(void*)*12 + 4);
v_self_4319_ = lean_ctor_get(v_a_4314_, 0);
v_heqProofs_4320_ = lean_ctor_get_uint8(v_a_4314_, sizeof(void*)*12 + 4);
lean_inc_ref(v_root_4043_);
v___x_4321_ = l_Lean_Expr_isTrue(v_root_4043_);
if (v___x_4321_ == 0)
{
uint8_t v___x_4322_; 
lean_inc_ref(v_root_4044_);
v___x_4322_ = l_Lean_Expr_isTrue(v_root_4044_);
if (v___x_4322_ == 0)
{
if (v_isHEq_4022_ == 0)
{
if (v_heqProofs_4318_ == 0)
{
if (v_heqProofs_4320_ == 0)
{
v___y_4214_ = v___x_4047_;
v___y_4215_ = v_a_4314_;
v___y_4216_ = v___y_4297_;
v___y_4217_ = v___y_4299_;
v___y_4218_ = v___y_4302_;
v___y_4219_ = v___y_4296_;
v___y_4220_ = v___y_4305_;
v___y_4221_ = v___y_4298_;
v___y_4222_ = v___y_4304_;
v___y_4223_ = v_a_4308_;
v_ctor_4224_ = v_ctor_4317_;
v___y_4225_ = v___y_4301_;
v___y_4226_ = v___x_4051_;
v___y_4227_ = v___y_4300_;
v___y_4228_ = v___y_4303_;
goto v___jp_4213_;
}
else
{
lean_inc_ref(v_self_4319_);
lean_inc_ref(v_self_4316_);
v___y_4269_ = v___y_4297_;
v___y_4270_ = v___y_4299_;
v___y_4271_ = v___y_4298_;
v___y_4272_ = v_a_4314_;
v___y_4273_ = v_self_4316_;
v___y_4274_ = v___y_4303_;
v___y_4275_ = v___x_4322_;
v___y_4276_ = v_self_4319_;
v___y_4277_ = v___y_4302_;
v___y_4278_ = v_a_4308_;
v___y_4279_ = v___y_4296_;
v___y_4280_ = v___y_4304_;
v___y_4281_ = v___y_4305_;
v___y_4282_ = v___y_4301_;
v___y_4283_ = v___y_4300_;
goto v___jp_4268_;
}
}
else
{
lean_inc_ref(v_self_4319_);
lean_inc_ref(v_self_4316_);
v___y_4269_ = v___y_4297_;
v___y_4270_ = v___y_4299_;
v___y_4271_ = v___y_4298_;
v___y_4272_ = v_a_4314_;
v___y_4273_ = v_self_4316_;
v___y_4274_ = v___y_4303_;
v___y_4275_ = v___x_4322_;
v___y_4276_ = v_self_4319_;
v___y_4277_ = v___y_4302_;
v___y_4278_ = v_a_4308_;
v___y_4279_ = v___y_4296_;
v___y_4280_ = v___y_4304_;
v___y_4281_ = v___y_4305_;
v___y_4282_ = v___y_4301_;
v___y_4283_ = v___y_4300_;
goto v___jp_4268_;
}
}
else
{
lean_inc_ref(v_self_4319_);
lean_inc_ref(v_self_4316_);
v___y_4269_ = v___y_4297_;
v___y_4270_ = v___y_4299_;
v___y_4271_ = v___y_4298_;
v___y_4272_ = v_a_4314_;
v___y_4273_ = v_self_4316_;
v___y_4274_ = v___y_4303_;
v___y_4275_ = v___x_4322_;
v___y_4276_ = v_self_4319_;
v___y_4277_ = v___y_4302_;
v___y_4278_ = v_a_4308_;
v___y_4279_ = v___y_4296_;
v___y_4280_ = v___y_4304_;
v___y_4281_ = v___y_4305_;
v___y_4282_ = v___y_4301_;
v___y_4283_ = v___y_4300_;
goto v___jp_4268_;
}
}
else
{
v___y_4255_ = v___y_4297_;
v___y_4256_ = v___y_4299_;
v___y_4257_ = v___y_4298_;
v___y_4258_ = v_a_4314_;
v___y_4259_ = v___y_4303_;
v___y_4260_ = v___y_4302_;
v___y_4261_ = v___y_4296_;
v___y_4262_ = v_a_4308_;
v___y_4263_ = v___y_4304_;
v___y_4264_ = v___y_4305_;
v___y_4265_ = v___y_4301_;
v___y_4266_ = v___y_4300_;
goto v___jp_4254_;
}
}
else
{
v___y_4255_ = v___y_4297_;
v___y_4256_ = v___y_4299_;
v___y_4257_ = v___y_4298_;
v___y_4258_ = v_a_4314_;
v___y_4259_ = v___y_4303_;
v___y_4260_ = v___y_4302_;
v___y_4261_ = v___y_4296_;
v___y_4262_ = v_a_4308_;
v___y_4263_ = v___y_4304_;
v___y_4264_ = v___y_4305_;
v___y_4265_ = v___y_4301_;
v___y_4266_ = v___y_4300_;
goto v___jp_4254_;
}
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec(v_a_4308_);
lean_dec(v_a_4042_);
lean_dec(v_a_4039_);
lean_dec_ref(v_proof_4021_);
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
v_a_4323_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4310_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4310_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec(v_a_4042_);
lean_dec(v_a_4039_);
lean_dec_ref(v_proof_4021_);
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
v_a_4331_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4307_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4307_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
else
{
lean_object* v_options_4377_; uint8_t v_hasTrace_4378_; 
lean_dec(v_a_4042_);
lean_dec(v_a_4039_);
lean_dec_ref(v_proof_4021_);
v_options_4377_ = lean_ctor_get(v_a_4031_, 2);
v_hasTrace_4378_ = lean_ctor_get_uint8(v_options_4377_, sizeof(void*)*1);
if (v_hasTrace_4378_ == 0)
{
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
goto v___jp_4034_;
}
else
{
lean_object* v_inheritedTraceOptions_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; uint8_t v___x_4382_; 
v_inheritedTraceOptions_4379_ = lean_ctor_get(v_a_4031_, 13);
v___x_4380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__0));
v___x_4381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_go___closed__1);
v___x_4382_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4379_, v_options_4377_, v___x_4381_);
if (v___x_4382_ == 0)
{
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
goto v___jp_4034_;
}
else
{
lean_object* v___x_4383_; 
v___x_4383_ = l_Lean_Meta_Grind_updateLastTag(v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v___x_4384_; 
lean_dec_ref_known(v___x_4383_, 1);
v___x_4384_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_lhs_4019_, v_a_4023_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = l_Lean_Meta_Grind_ppENodeRef___redArg(v_rhs_4020_, v_a_4023_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_a_4387_);
lean_dec_ref_known(v___x_4386_, 1);
v___x_4388_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__6);
v___x_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4389_, 0, v_a_4385_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
lean_ctor_set(v___x_4390_, 1, v_a_4387_);
v___x_4391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___closed__8);
v___x_4392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4390_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_4380_, v___x_4392_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_dec_ref_known(v___x_4393_, 1);
goto v___jp_4034_;
}
else
{
return v___x_4393_;
}
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
lean_dec(v_a_4385_);
v_a_4394_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___x_4386_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4386_);
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
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec_ref(v_rhs_4020_);
v_a_4402_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4384_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4384_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
else
{
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
return v___x_4383_;
}
}
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_dec(v_a_4039_);
lean_dec_ref(v_proof_4021_);
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
v_a_4410_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4041_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4041_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec_ref(v_proof_4021_);
lean_dec_ref(v_rhs_4020_);
lean_dec_ref(v_lhs_4019_);
v_a_4418_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4038_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4038_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
v___jp_4034_:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = lean_box(0);
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
return v___x_4036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep___boxed(lean_object* v_lhs_4426_, lean_object* v_rhs_4427_, lean_object* v_proof_4428_, lean_object* v_isHEq_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_){
_start:
{
uint8_t v_isHEq_boxed_4441_; lean_object* v_res_4442_; 
v_isHEq_boxed_4441_ = lean_unbox(v_isHEq_4429_);
v_res_4442_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4426_, v_rhs_4427_, v_proof_4428_, v_isHEq_boxed_4441_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_);
lean_dec(v_a_4439_);
lean_dec_ref(v_a_4438_);
lean_dec(v_a_4437_);
lean_dec_ref(v_a_4436_);
lean_dec(v_a_4435_);
lean_dec_ref(v_a_4434_);
lean_dec(v_a_4433_);
lean_dec_ref(v_a_4432_);
lean_dec(v_a_4431_);
lean_dec(v_a_4430_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(lean_object* v_a_4445_){
_start:
{
lean_object* v___x_4447_; lean_object* v_toGoalState_4448_; lean_object* v_mvarId_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4485_; 
v___x_4447_ = lean_st_ref_take(v_a_4445_);
v_toGoalState_4448_ = lean_ctor_get(v___x_4447_, 0);
v_mvarId_4449_ = lean_ctor_get(v___x_4447_, 1);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4451_ = v___x_4447_;
v_isShared_4452_ = v_isSharedCheck_4485_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_mvarId_4449_);
lean_inc(v_toGoalState_4448_);
lean_dec(v___x_4447_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4485_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v_nextDeclIdx_4453_; lean_object* v_enodeMap_4454_; lean_object* v_exprs_4455_; lean_object* v_parents_4456_; lean_object* v_congrTable_4457_; lean_object* v_appMap_4458_; lean_object* v_indicesFound_4459_; uint8_t v_inconsistent_4460_; lean_object* v_nextIdx_4461_; lean_object* v_newRawFacts_4462_; lean_object* v_facts_4463_; lean_object* v_extThms_4464_; lean_object* v_ematch_4465_; lean_object* v_inj_4466_; lean_object* v_split_4467_; lean_object* v_clean_4468_; lean_object* v_sstates_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4483_; 
v_nextDeclIdx_4453_ = lean_ctor_get(v_toGoalState_4448_, 0);
v_enodeMap_4454_ = lean_ctor_get(v_toGoalState_4448_, 1);
v_exprs_4455_ = lean_ctor_get(v_toGoalState_4448_, 2);
v_parents_4456_ = lean_ctor_get(v_toGoalState_4448_, 3);
v_congrTable_4457_ = lean_ctor_get(v_toGoalState_4448_, 4);
v_appMap_4458_ = lean_ctor_get(v_toGoalState_4448_, 5);
v_indicesFound_4459_ = lean_ctor_get(v_toGoalState_4448_, 6);
v_inconsistent_4460_ = lean_ctor_get_uint8(v_toGoalState_4448_, sizeof(void*)*17);
v_nextIdx_4461_ = lean_ctor_get(v_toGoalState_4448_, 8);
v_newRawFacts_4462_ = lean_ctor_get(v_toGoalState_4448_, 9);
v_facts_4463_ = lean_ctor_get(v_toGoalState_4448_, 10);
v_extThms_4464_ = lean_ctor_get(v_toGoalState_4448_, 11);
v_ematch_4465_ = lean_ctor_get(v_toGoalState_4448_, 12);
v_inj_4466_ = lean_ctor_get(v_toGoalState_4448_, 13);
v_split_4467_ = lean_ctor_get(v_toGoalState_4448_, 14);
v_clean_4468_ = lean_ctor_get(v_toGoalState_4448_, 15);
v_sstates_4469_ = lean_ctor_get(v_toGoalState_4448_, 16);
v_isSharedCheck_4483_ = !lean_is_exclusive(v_toGoalState_4448_);
if (v_isSharedCheck_4483_ == 0)
{
lean_object* v_unused_4484_; 
v_unused_4484_ = lean_ctor_get(v_toGoalState_4448_, 7);
lean_dec(v_unused_4484_);
v___x_4471_ = v_toGoalState_4448_;
v_isShared_4472_ = v_isSharedCheck_4483_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_sstates_4469_);
lean_inc(v_clean_4468_);
lean_inc(v_split_4467_);
lean_inc(v_inj_4466_);
lean_inc(v_ematch_4465_);
lean_inc(v_extThms_4464_);
lean_inc(v_facts_4463_);
lean_inc(v_newRawFacts_4462_);
lean_inc(v_nextIdx_4461_);
lean_inc(v_indicesFound_4459_);
lean_inc(v_appMap_4458_);
lean_inc(v_congrTable_4457_);
lean_inc(v_parents_4456_);
lean_inc(v_exprs_4455_);
lean_inc(v_enodeMap_4454_);
lean_inc(v_nextDeclIdx_4453_);
lean_dec(v_toGoalState_4448_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4483_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___closed__0));
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 7, v___x_4473_);
v___x_4475_ = v___x_4471_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_nextDeclIdx_4453_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v_enodeMap_4454_);
lean_ctor_set(v_reuseFailAlloc_4482_, 2, v_exprs_4455_);
lean_ctor_set(v_reuseFailAlloc_4482_, 3, v_parents_4456_);
lean_ctor_set(v_reuseFailAlloc_4482_, 4, v_congrTable_4457_);
lean_ctor_set(v_reuseFailAlloc_4482_, 5, v_appMap_4458_);
lean_ctor_set(v_reuseFailAlloc_4482_, 6, v_indicesFound_4459_);
lean_ctor_set(v_reuseFailAlloc_4482_, 7, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4482_, 8, v_nextIdx_4461_);
lean_ctor_set(v_reuseFailAlloc_4482_, 9, v_newRawFacts_4462_);
lean_ctor_set(v_reuseFailAlloc_4482_, 10, v_facts_4463_);
lean_ctor_set(v_reuseFailAlloc_4482_, 11, v_extThms_4464_);
lean_ctor_set(v_reuseFailAlloc_4482_, 12, v_ematch_4465_);
lean_ctor_set(v_reuseFailAlloc_4482_, 13, v_inj_4466_);
lean_ctor_set(v_reuseFailAlloc_4482_, 14, v_split_4467_);
lean_ctor_set(v_reuseFailAlloc_4482_, 15, v_clean_4468_);
lean_ctor_set(v_reuseFailAlloc_4482_, 16, v_sstates_4469_);
lean_ctor_set_uint8(v_reuseFailAlloc_4482_, sizeof(void*)*17, v_inconsistent_4460_);
v___x_4475_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4477_; 
if (v_isShared_4452_ == 0)
{
lean_ctor_set(v___x_4451_, 0, v___x_4475_);
v___x_4477_ = v___x_4451_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_mvarId_4449_);
v___x_4477_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = lean_st_ref_put(v_a_4445_, v___x_4477_);
v___x_4479_ = lean_box(0);
v___x_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
return v___x_4480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg___boxed(lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4486_);
lean_dec(v_a_4486_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___redArg(v_a_4489_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts___boxed(lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_resetNewFacts(v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
lean_dec(v_a_4506_);
lean_dec_ref(v_a_4505_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_a_4502_);
lean_dec(v_a_4501_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(lean_object* v_a_4513_){
_start:
{
lean_object* v___x_4515_; lean_object* v_toGoalState_4516_; lean_object* v_newFacts_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; uint8_t v___x_4521_; 
v___x_4515_ = lean_st_ref_get(v_a_4513_);
v_toGoalState_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc_ref(v_toGoalState_4516_);
lean_dec(v___x_4515_);
v_newFacts_4517_ = lean_ctor_get(v_toGoalState_4516_, 7);
lean_inc_ref(v_newFacts_4517_);
lean_dec_ref(v_toGoalState_4516_);
v___x_4518_ = lean_array_get_size(v_newFacts_4517_);
v___x_4519_ = lean_unsigned_to_nat(1u);
v___x_4520_ = lean_nat_sub(v___x_4518_, v___x_4519_);
v___x_4521_ = lean_nat_dec_lt(v___x_4520_, v___x_4518_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
lean_dec(v___x_4520_);
lean_dec_ref(v_newFacts_4517_);
v___x_4522_ = lean_box(0);
v___x_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
return v___x_4523_;
}
else
{
lean_object* v___x_4524_; lean_object* v_toGoalState_4525_; lean_object* v_mvarId_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4563_; 
v___x_4524_ = lean_st_ref_take(v_a_4513_);
v_toGoalState_4525_ = lean_ctor_get(v___x_4524_, 0);
v_mvarId_4526_ = lean_ctor_get(v___x_4524_, 1);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4528_ = v___x_4524_;
v_isShared_4529_ = v_isSharedCheck_4563_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_mvarId_4526_);
lean_inc(v_toGoalState_4525_);
lean_dec(v___x_4524_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4563_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v_nextDeclIdx_4530_; lean_object* v_enodeMap_4531_; lean_object* v_exprs_4532_; lean_object* v_parents_4533_; lean_object* v_congrTable_4534_; lean_object* v_appMap_4535_; lean_object* v_indicesFound_4536_; lean_object* v_newFacts_4537_; uint8_t v_inconsistent_4538_; lean_object* v_nextIdx_4539_; lean_object* v_newRawFacts_4540_; lean_object* v_facts_4541_; lean_object* v_extThms_4542_; lean_object* v_ematch_4543_; lean_object* v_inj_4544_; lean_object* v_split_4545_; lean_object* v_clean_4546_; lean_object* v_sstates_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4562_; 
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
v_isSharedCheck_4562_ = !lean_is_exclusive(v_toGoalState_4525_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4549_ = v_toGoalState_4525_;
v_isShared_4550_ = v_isSharedCheck_4562_;
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
v_isShared_4550_ = v_isSharedCheck_4562_;
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
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_nextDeclIdx_4530_);
lean_ctor_set(v_reuseFailAlloc_4561_, 1, v_enodeMap_4531_);
lean_ctor_set(v_reuseFailAlloc_4561_, 2, v_exprs_4532_);
lean_ctor_set(v_reuseFailAlloc_4561_, 3, v_parents_4533_);
lean_ctor_set(v_reuseFailAlloc_4561_, 4, v_congrTable_4534_);
lean_ctor_set(v_reuseFailAlloc_4561_, 5, v_appMap_4535_);
lean_ctor_set(v_reuseFailAlloc_4561_, 6, v_indicesFound_4536_);
lean_ctor_set(v_reuseFailAlloc_4561_, 7, v___x_4551_);
lean_ctor_set(v_reuseFailAlloc_4561_, 8, v_nextIdx_4539_);
lean_ctor_set(v_reuseFailAlloc_4561_, 9, v_newRawFacts_4540_);
lean_ctor_set(v_reuseFailAlloc_4561_, 10, v_facts_4541_);
lean_ctor_set(v_reuseFailAlloc_4561_, 11, v_extThms_4542_);
lean_ctor_set(v_reuseFailAlloc_4561_, 12, v_ematch_4543_);
lean_ctor_set(v_reuseFailAlloc_4561_, 13, v_inj_4544_);
lean_ctor_set(v_reuseFailAlloc_4561_, 14, v_split_4545_);
lean_ctor_set(v_reuseFailAlloc_4561_, 15, v_clean_4546_);
lean_ctor_set(v_reuseFailAlloc_4561_, 16, v_sstates_4547_);
lean_ctor_set_uint8(v_reuseFailAlloc_4561_, sizeof(void*)*17, v_inconsistent_4538_);
v___x_4553_ = v_reuseFailAlloc_4561_;
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
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4553_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v_mvarId_4526_);
v___x_4555_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4556_ = lean_st_ref_put(v_a_4513_, v___x_4555_);
v___x_4557_ = lean_array_fget(v_newFacts_4517_, v___x_4520_);
lean_dec(v___x_4520_);
lean_dec_ref(v_newFacts_4517_);
v___x_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
v___x_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4558_);
return v___x_4559_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg___boxed(lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4564_);
lean_dec(v_a_4564_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v___x_4578_; 
v___x_4578_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___redArg(v_a_4567_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f___boxed(lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_popNextFact_x3f(v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
lean_dec(v_a_4586_);
lean_dec_ref(v_a_4585_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
lean_dec(v_a_4582_);
lean_dec_ref(v_a_4581_);
lean_dec(v_a_4580_);
lean_dec(v_a_4579_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(lean_object* v_lhs_4591_, lean_object* v_rhs_4592_, lean_object* v_proof_4593_, uint8_t v_isHEq_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v___x_4606_; 
v___x_4606_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep(v_lhs_4591_, v_rhs_4592_, v_proof_4593_, v_isHEq_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v___x_4607_; 
lean_dec_ref_known(v___x_4606_, 1);
lean_inc(v_a_4604_);
lean_inc_ref(v_a_4603_);
lean_inc(v_a_4602_);
lean_inc_ref(v_a_4601_);
lean_inc(v_a_4600_);
lean_inc_ref(v_a_4599_);
lean_inc(v_a_4598_);
lean_inc_ref(v_a_4597_);
lean_inc(v_a_4596_);
lean_inc(v_a_4595_);
v___x_4607_ = lean_grind_process_new_facts(v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
return v___x_4607_;
}
else
{
return v___x_4606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore___boxed(lean_object* v_lhs_4608_, lean_object* v_rhs_4609_, lean_object* v_proof_4610_, lean_object* v_isHEq_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_){
_start:
{
uint8_t v_isHEq_boxed_4623_; lean_object* v_res_4624_; 
v_isHEq_boxed_4623_ = lean_unbox(v_isHEq_4611_);
v_res_4624_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4608_, v_rhs_4609_, v_proof_4610_, v_isHEq_boxed_4623_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4620_);
lean_dec(v_a_4619_);
lean_dec_ref(v_a_4618_);
lean_dec(v_a_4617_);
lean_dec_ref(v_a_4616_);
lean_dec(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec(v_a_4613_);
lean_dec(v_a_4612_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(lean_object* v_lhs_4625_, lean_object* v_rhs_4626_, lean_object* v_proof_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_){
_start:
{
uint8_t v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = 0;
v___x_4640_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4625_, v_rhs_4626_, v_proof_4627_, v___x_4639_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq___boxed(lean_object* v_lhs_4641_, lean_object* v_rhs_4642_, lean_object* v_proof_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4641_, v_rhs_4642_, v_proof_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
lean_dec(v_a_4653_);
lean_dec_ref(v_a_4652_);
lean_dec(v_a_4651_);
lean_dec_ref(v_a_4650_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
lean_dec(v_a_4644_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(lean_object* v_lhs_4656_, lean_object* v_rhs_4657_, lean_object* v_proof_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
uint8_t v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = 1;
v___x_4671_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4656_, v_rhs_4657_, v_proof_4658_, v___x_4670_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq___boxed(lean_object* v_lhs_4672_, lean_object* v_rhs_4673_, lean_object* v_proof_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addHEq(v_lhs_4672_, v_rhs_4673_, v_proof_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_);
lean_dec(v_a_4684_);
lean_dec_ref(v_a_4683_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
lean_dec(v_a_4676_);
lean_dec(v_a_4675_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(lean_object* v_fact_4687_, lean_object* v_a_4688_){
_start:
{
lean_object* v___x_4690_; lean_object* v_toGoalState_4691_; lean_object* v_mvarId_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4728_; 
v___x_4690_ = lean_st_ref_take(v_a_4688_);
v_toGoalState_4691_ = lean_ctor_get(v___x_4690_, 0);
v_mvarId_4692_ = lean_ctor_get(v___x_4690_, 1);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4694_ = v___x_4690_;
v_isShared_4695_ = v_isSharedCheck_4728_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_mvarId_4692_);
lean_inc(v_toGoalState_4691_);
lean_dec(v___x_4690_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4728_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v_nextDeclIdx_4696_; lean_object* v_enodeMap_4697_; lean_object* v_exprs_4698_; lean_object* v_parents_4699_; lean_object* v_congrTable_4700_; lean_object* v_appMap_4701_; lean_object* v_indicesFound_4702_; lean_object* v_newFacts_4703_; uint8_t v_inconsistent_4704_; lean_object* v_nextIdx_4705_; lean_object* v_newRawFacts_4706_; lean_object* v_facts_4707_; lean_object* v_extThms_4708_; lean_object* v_ematch_4709_; lean_object* v_inj_4710_; lean_object* v_split_4711_; lean_object* v_clean_4712_; lean_object* v_sstates_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4727_; 
v_nextDeclIdx_4696_ = lean_ctor_get(v_toGoalState_4691_, 0);
v_enodeMap_4697_ = lean_ctor_get(v_toGoalState_4691_, 1);
v_exprs_4698_ = lean_ctor_get(v_toGoalState_4691_, 2);
v_parents_4699_ = lean_ctor_get(v_toGoalState_4691_, 3);
v_congrTable_4700_ = lean_ctor_get(v_toGoalState_4691_, 4);
v_appMap_4701_ = lean_ctor_get(v_toGoalState_4691_, 5);
v_indicesFound_4702_ = lean_ctor_get(v_toGoalState_4691_, 6);
v_newFacts_4703_ = lean_ctor_get(v_toGoalState_4691_, 7);
v_inconsistent_4704_ = lean_ctor_get_uint8(v_toGoalState_4691_, sizeof(void*)*17);
v_nextIdx_4705_ = lean_ctor_get(v_toGoalState_4691_, 8);
v_newRawFacts_4706_ = lean_ctor_get(v_toGoalState_4691_, 9);
v_facts_4707_ = lean_ctor_get(v_toGoalState_4691_, 10);
v_extThms_4708_ = lean_ctor_get(v_toGoalState_4691_, 11);
v_ematch_4709_ = lean_ctor_get(v_toGoalState_4691_, 12);
v_inj_4710_ = lean_ctor_get(v_toGoalState_4691_, 13);
v_split_4711_ = lean_ctor_get(v_toGoalState_4691_, 14);
v_clean_4712_ = lean_ctor_get(v_toGoalState_4691_, 15);
v_sstates_4713_ = lean_ctor_get(v_toGoalState_4691_, 16);
v_isSharedCheck_4727_ = !lean_is_exclusive(v_toGoalState_4691_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4715_ = v_toGoalState_4691_;
v_isShared_4716_ = v_isSharedCheck_4727_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_sstates_4713_);
lean_inc(v_clean_4712_);
lean_inc(v_split_4711_);
lean_inc(v_inj_4710_);
lean_inc(v_ematch_4709_);
lean_inc(v_extThms_4708_);
lean_inc(v_facts_4707_);
lean_inc(v_newRawFacts_4706_);
lean_inc(v_nextIdx_4705_);
lean_inc(v_newFacts_4703_);
lean_inc(v_indicesFound_4702_);
lean_inc(v_appMap_4701_);
lean_inc(v_congrTable_4700_);
lean_inc(v_parents_4699_);
lean_inc(v_exprs_4698_);
lean_inc(v_enodeMap_4697_);
lean_inc(v_nextDeclIdx_4696_);
lean_dec(v_toGoalState_4691_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4727_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4717_; lean_object* v___x_4719_; 
v___x_4717_ = l_Lean_PersistentArray_push___redArg(v_facts_4707_, v_fact_4687_);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 10, v___x_4717_);
v___x_4719_ = v___x_4715_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_nextDeclIdx_4696_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v_enodeMap_4697_);
lean_ctor_set(v_reuseFailAlloc_4726_, 2, v_exprs_4698_);
lean_ctor_set(v_reuseFailAlloc_4726_, 3, v_parents_4699_);
lean_ctor_set(v_reuseFailAlloc_4726_, 4, v_congrTable_4700_);
lean_ctor_set(v_reuseFailAlloc_4726_, 5, v_appMap_4701_);
lean_ctor_set(v_reuseFailAlloc_4726_, 6, v_indicesFound_4702_);
lean_ctor_set(v_reuseFailAlloc_4726_, 7, v_newFacts_4703_);
lean_ctor_set(v_reuseFailAlloc_4726_, 8, v_nextIdx_4705_);
lean_ctor_set(v_reuseFailAlloc_4726_, 9, v_newRawFacts_4706_);
lean_ctor_set(v_reuseFailAlloc_4726_, 10, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4726_, 11, v_extThms_4708_);
lean_ctor_set(v_reuseFailAlloc_4726_, 12, v_ematch_4709_);
lean_ctor_set(v_reuseFailAlloc_4726_, 13, v_inj_4710_);
lean_ctor_set(v_reuseFailAlloc_4726_, 14, v_split_4711_);
lean_ctor_set(v_reuseFailAlloc_4726_, 15, v_clean_4712_);
lean_ctor_set(v_reuseFailAlloc_4726_, 16, v_sstates_4713_);
lean_ctor_set_uint8(v_reuseFailAlloc_4726_, sizeof(void*)*17, v_inconsistent_4704_);
v___x_4719_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
lean_object* v___x_4721_; 
if (v_isShared_4695_ == 0)
{
lean_ctor_set(v___x_4694_, 0, v___x_4719_);
v___x_4721_ = v___x_4694_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4719_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v_mvarId_4692_);
v___x_4721_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4722_ = lean_st_ref_put(v_a_4688_, v___x_4721_);
v___x_4723_ = lean_box(0);
v___x_4724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4723_);
return v___x_4724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg___boxed(lean_object* v_fact_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4729_, v_a_4730_);
lean_dec(v_a_4730_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(lean_object* v_fact_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_4733_, v_a_4734_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___boxed(lean_object* v_fact_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact(v_fact_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec(v_a_4754_);
lean_dec_ref(v_a_4753_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
lean_dec(v_a_4748_);
lean_dec(v_a_4747_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq(lean_object* v_lhs_4759_, lean_object* v_rhs_4760_, lean_object* v_proof_4761_, lean_object* v_generation_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v___x_4774_; 
lean_inc_ref(v_rhs_4760_);
lean_inc_ref(v_lhs_4759_);
v___x_4774_ = l_Lean_Meta_mkEq(v_lhs_4759_, v_rhs_4760_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_object* v_a_4775_; lean_object* v___x_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4786_; 
v_a_4775_ = lean_ctor_get(v___x_4774_, 0);
lean_inc_n(v_a_4775_, 2);
lean_dec_ref_known(v___x_4774_, 1);
v___x_4776_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_a_4775_, v_a_4763_);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4786_ == 0)
{
lean_object* v_unused_4787_; 
v_unused_4787_ = lean_ctor_get(v___x_4776_, 0);
lean_dec(v_unused_4787_);
v___x_4778_ = v___x_4776_;
v_isShared_4779_ = v_isSharedCheck_4786_;
goto v_resetjp_4777_;
}
else
{
lean_dec(v___x_4776_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4786_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4781_; 
if (v_isShared_4779_ == 0)
{
lean_ctor_set_tag(v___x_4778_, 1);
lean_ctor_set(v___x_4778_, 0, v_a_4775_);
v___x_4781_ = v___x_4778_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4775_);
v___x_4781_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4782_; 
lean_inc(v_a_4772_);
lean_inc_ref(v_a_4771_);
lean_inc(v_a_4770_);
lean_inc_ref(v_a_4769_);
lean_inc(v_a_4768_);
lean_inc_ref(v_a_4767_);
lean_inc(v_a_4766_);
lean_inc_ref(v_a_4765_);
lean_inc(v_a_4764_);
lean_inc(v_a_4763_);
lean_inc_ref(v___x_4781_);
lean_inc(v_generation_4762_);
lean_inc_ref(v_lhs_4759_);
v___x_4782_ = lean_grind_internalize(v_lhs_4759_, v_generation_4762_, v___x_4781_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v___x_4783_; 
lean_dec_ref_known(v___x_4782_, 1);
lean_inc(v_a_4772_);
lean_inc_ref(v_a_4771_);
lean_inc(v_a_4770_);
lean_inc_ref(v_a_4769_);
lean_inc(v_a_4768_);
lean_inc_ref(v_a_4767_);
lean_inc(v_a_4766_);
lean_inc_ref(v_a_4765_);
lean_inc(v_a_4764_);
lean_inc(v_a_4763_);
lean_inc_ref(v_rhs_4760_);
v___x_4783_ = lean_grind_internalize(v_rhs_4760_, v_generation_4762_, v___x_4781_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v___x_4784_; 
lean_dec_ref_known(v___x_4783_, 1);
v___x_4784_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_lhs_4759_, v_rhs_4760_, v_proof_4761_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
return v___x_4784_;
}
else
{
lean_dec_ref(v_proof_4761_);
lean_dec_ref(v_rhs_4760_);
lean_dec_ref(v_lhs_4759_);
return v___x_4783_;
}
}
else
{
lean_dec_ref(v___x_4781_);
lean_dec(v_generation_4762_);
lean_dec_ref(v_proof_4761_);
lean_dec_ref(v_rhs_4760_);
lean_dec_ref(v_lhs_4759_);
return v___x_4782_;
}
}
}
}
else
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4795_; 
lean_dec(v_generation_4762_);
lean_dec_ref(v_proof_4761_);
lean_dec_ref(v_rhs_4760_);
lean_dec_ref(v_lhs_4759_);
v_a_4788_ = lean_ctor_get(v___x_4774_, 0);
v_isSharedCheck_4795_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4795_ == 0)
{
v___x_4790_ = v___x_4774_;
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4774_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4795_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4793_; 
if (v_isShared_4791_ == 0)
{
v___x_4793_ = v___x_4790_;
goto v_reusejp_4792_;
}
else
{
lean_object* v_reuseFailAlloc_4794_; 
v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_a_4788_);
v___x_4793_ = v_reuseFailAlloc_4794_;
goto v_reusejp_4792_;
}
v_reusejp_4792_:
{
return v___x_4793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addNewEq___boxed(lean_object* v_lhs_4796_, lean_object* v_rhs_4797_, lean_object* v_proof_4798_, lean_object* v_generation_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l_Lean_Meta_Grind_addNewEq(v_lhs_4796_, v_rhs_4797_, v_proof_4798_, v_generation_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_a_4804_);
lean_dec(v_a_4803_);
lean_dec_ref(v_a_4802_);
lean_dec(v_a_4801_);
lean_dec(v_a_4800_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(lean_object* v_proof_4812_, lean_object* v_generation_4813_, lean_object* v_p_4814_, uint8_t v_isNeg_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = lean_box(0);
lean_inc(v_a_4825_);
lean_inc_ref(v_a_4824_);
lean_inc(v_a_4823_);
lean_inc_ref(v_a_4822_);
lean_inc(v_a_4821_);
lean_inc_ref(v_a_4820_);
lean_inc(v_a_4819_);
lean_inc_ref(v_a_4818_);
lean_inc(v_a_4817_);
lean_inc(v_a_4816_);
lean_inc_ref(v_p_4814_);
v___x_4828_ = lean_grind_internalize(v_p_4814_, v_generation_4813_, v___x_4827_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_dec_ref_known(v___x_4828_, 1);
if (v_isNeg_4815_ == 0)
{
lean_object* v___x_4829_; 
v___x_4829_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_4820_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v_a_4830_; lean_object* v___x_4831_; 
v_a_4830_ = lean_ctor_get(v___x_4829_, 0);
lean_inc(v_a_4830_);
lean_dec_ref_known(v___x_4829_, 1);
v___x_4831_ = l_Lean_Meta_mkEqTrue(v_proof_4812_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v_a_4832_; lean_object* v___x_4833_; 
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
lean_inc(v_a_4832_);
lean_dec_ref_known(v___x_4831_, 1);
v___x_4833_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4814_, v_a_4830_, v_a_4832_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
return v___x_4833_;
}
else
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4841_; 
lean_dec(v_a_4830_);
lean_dec_ref(v_p_4814_);
v_a_4834_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4836_ = v___x_4831_;
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4831_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4841_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4839_; 
if (v_isShared_4837_ == 0)
{
v___x_4839_ = v___x_4836_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
lean_dec_ref(v_p_4814_);
lean_dec_ref(v_proof_4812_);
v_a_4842_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4844_ = v___x_4829_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4829_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
else
{
lean_object* v___x_4850_; 
v___x_4850_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4820_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4852_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_a_4851_);
lean_dec_ref_known(v___x_4850_, 1);
v___x_4852_ = l_Lean_Meta_mkEqFalse(v_proof_4812_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; lean_object* v___x_4854_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc(v_a_4853_);
lean_dec_ref_known(v___x_4852_, 1);
v___x_4854_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4814_, v_a_4851_, v_a_4853_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
return v___x_4854_;
}
else
{
lean_object* v_a_4855_; lean_object* v___x_4857_; uint8_t v_isShared_4858_; uint8_t v_isSharedCheck_4862_; 
lean_dec(v_a_4851_);
lean_dec_ref(v_p_4814_);
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
lean_dec_ref(v_p_4814_);
lean_dec_ref(v_proof_4812_);
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
}
else
{
lean_dec_ref(v_p_4814_);
lean_dec_ref(v_proof_4812_);
return v___x_4828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact___boxed(lean_object* v_proof_4871_, lean_object* v_generation_4872_, lean_object* v_p_4873_, lean_object* v_isNeg_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
uint8_t v_isNeg_boxed_4886_; lean_object* v_res_4887_; 
v_isNeg_boxed_4886_ = lean_unbox(v_isNeg_4874_);
v_res_4887_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4871_, v_generation_4872_, v_p_4873_, v_isNeg_boxed_4886_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
lean_dec(v_a_4884_);
lean_dec_ref(v_a_4883_);
lean_dec(v_a_4882_);
lean_dec_ref(v_a_4881_);
lean_dec(v_a_4880_);
lean_dec_ref(v_a_4879_);
lean_dec(v_a_4878_);
lean_dec_ref(v_a_4877_);
lean_dec(v_a_4876_);
lean_dec(v_a_4875_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(lean_object* v_proof_4888_, lean_object* v_generation_4889_, lean_object* v_p_4890_, lean_object* v_lhs_4891_, lean_object* v_rhs_4892_, uint8_t v_isNeg_4893_, uint8_t v_isHEq_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_){
_start:
{
if (v_isNeg_4893_ == 0)
{
lean_object* v___x_4906_; lean_object* v___x_4907_; 
lean_inc_ref(v_p_4890_);
v___x_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4906_, 0, v_p_4890_);
lean_inc(v_a_4904_);
lean_inc_ref(v_a_4903_);
lean_inc(v_a_4902_);
lean_inc_ref(v_a_4901_);
lean_inc(v_a_4900_);
lean_inc_ref(v_a_4899_);
lean_inc(v_a_4898_);
lean_inc_ref(v_a_4897_);
lean_inc(v_a_4896_);
lean_inc(v_a_4895_);
lean_inc_ref(v___x_4906_);
lean_inc(v_generation_4889_);
lean_inc_ref(v_lhs_4891_);
v___x_4907_ = lean_grind_internalize(v_lhs_4891_, v_generation_4889_, v___x_4906_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v___x_4908_; 
lean_dec_ref_known(v___x_4907_, 1);
lean_inc(v_a_4904_);
lean_inc_ref(v_a_4903_);
lean_inc(v_a_4902_);
lean_inc_ref(v_a_4901_);
lean_inc(v_a_4900_);
lean_inc_ref(v_a_4899_);
lean_inc(v_a_4898_);
lean_inc_ref(v_a_4897_);
lean_inc(v_a_4896_);
lean_inc(v_a_4895_);
lean_inc_ref(v_rhs_4892_);
v___x_4908_ = lean_grind_internalize(v_rhs_4892_, v_generation_4889_, v___x_4906_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v___x_4909_; lean_object* v___x_4910_; 
lean_dec_ref_known(v___x_4908_, 1);
v___x_4909_ = lean_box(0);
v___x_4910_ = l_Lean_Meta_Grind_Solvers_internalize(v_p_4890_, v___x_4909_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v___x_4911_; 
lean_dec_ref_known(v___x_4910_, 1);
v___x_4911_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqCore(v_lhs_4891_, v_rhs_4892_, v_proof_4888_, v_isHEq_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_);
return v___x_4911_;
}
else
{
lean_dec_ref(v_rhs_4892_);
lean_dec_ref(v_lhs_4891_);
lean_dec_ref(v_proof_4888_);
return v___x_4910_;
}
}
else
{
lean_dec_ref(v_rhs_4892_);
lean_dec_ref(v_lhs_4891_);
lean_dec_ref(v_p_4890_);
lean_dec_ref(v_proof_4888_);
return v___x_4908_;
}
}
else
{
lean_dec_ref_known(v___x_4906_, 1);
lean_dec_ref(v_rhs_4892_);
lean_dec_ref(v_lhs_4891_);
lean_dec_ref(v_p_4890_);
lean_dec(v_generation_4889_);
lean_dec_ref(v_proof_4888_);
return v___x_4907_;
}
}
else
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
lean_dec_ref(v_rhs_4892_);
lean_dec_ref(v_lhs_4891_);
v___x_4912_ = lean_box(0);
lean_inc(v_a_4904_);
lean_inc_ref(v_a_4903_);
lean_inc(v_a_4902_);
lean_inc_ref(v_a_4901_);
lean_inc(v_a_4900_);
lean_inc_ref(v_a_4899_);
lean_inc(v_a_4898_);
lean_inc_ref(v_a_4897_);
lean_inc(v_a_4896_);
lean_inc(v_a_4895_);
lean_inc_ref(v_p_4890_);
v___x_4913_ = lean_grind_internalize(v_p_4890_, v_generation_4889_, v___x_4912_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v___x_4914_; 
lean_dec_ref_known(v___x_4913_, 1);
v___x_4914_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_4899_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4916_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc(v_a_4915_);
lean_dec_ref_known(v___x_4914_, 1);
v___x_4916_ = l_Lean_Meta_mkEqFalse(v_proof_4888_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_);
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v_a_4917_; lean_object* v___x_4918_; 
v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
lean_inc(v_a_4917_);
lean_dec_ref_known(v___x_4916_, 1);
v___x_4918_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEq(v_p_4890_, v_a_4915_, v_a_4917_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_);
return v___x_4918_;
}
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
lean_dec(v_a_4915_);
lean_dec_ref(v_p_4890_);
v_a_4919_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___x_4916_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4916_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4924_; 
if (v_isShared_4922_ == 0)
{
v___x_4924_ = v___x_4921_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_a_4919_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
else
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4934_; 
lean_dec_ref(v_p_4890_);
lean_dec_ref(v_proof_4888_);
v_a_4927_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4929_ = v___x_4914_;
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4914_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4932_; 
if (v_isShared_4930_ == 0)
{
v___x_4932_ = v___x_4929_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v_a_4927_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
}
else
{
lean_dec_ref(v_p_4890_);
lean_dec_ref(v_proof_4888_);
return v___x_4913_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq___boxed(lean_object** _args){
lean_object* v_proof_4935_ = _args[0];
lean_object* v_generation_4936_ = _args[1];
lean_object* v_p_4937_ = _args[2];
lean_object* v_lhs_4938_ = _args[3];
lean_object* v_rhs_4939_ = _args[4];
lean_object* v_isNeg_4940_ = _args[5];
lean_object* v_isHEq_4941_ = _args[6];
lean_object* v_a_4942_ = _args[7];
lean_object* v_a_4943_ = _args[8];
lean_object* v_a_4944_ = _args[9];
lean_object* v_a_4945_ = _args[10];
lean_object* v_a_4946_ = _args[11];
lean_object* v_a_4947_ = _args[12];
lean_object* v_a_4948_ = _args[13];
lean_object* v_a_4949_ = _args[14];
lean_object* v_a_4950_ = _args[15];
lean_object* v_a_4951_ = _args[16];
lean_object* v_a_4952_ = _args[17];
_start:
{
uint8_t v_isNeg_boxed_4953_; uint8_t v_isHEq_boxed_4954_; lean_object* v_res_4955_; 
v_isNeg_boxed_4953_ = lean_unbox(v_isNeg_4940_);
v_isHEq_boxed_4954_ = lean_unbox(v_isHEq_4941_);
v_res_4955_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4935_, v_generation_4936_, v_p_4937_, v_lhs_4938_, v_rhs_4939_, v_isNeg_boxed_4953_, v_isHEq_boxed_4954_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_);
lean_dec(v_a_4951_);
lean_dec_ref(v_a_4950_);
lean_dec(v_a_4949_);
lean_dec_ref(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_a_4946_);
lean_dec(v_a_4945_);
lean_dec_ref(v_a_4944_);
lean_dec(v_a_4943_);
lean_dec(v_a_4942_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(lean_object* v_proof_4959_, lean_object* v_generation_4960_, lean_object* v_p_4961_, uint8_t v_isNeg_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_){
_start:
{
lean_object* v___x_4974_; 
lean_inc_ref(v_p_4961_);
v___x_4974_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_p_4961_, v_a_4970_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4976_; uint8_t v___x_4977_; 
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_a_4975_);
lean_dec_ref_known(v___x_4974_, 1);
v___x_4976_ = l_Lean_Expr_cleanupAnnotations(v_a_4975_);
v___x_4977_ = l_Lean_Expr_isApp(v___x_4976_);
if (v___x_4977_ == 0)
{
lean_object* v___x_4978_; 
lean_dec_ref(v___x_4976_);
v___x_4978_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4959_, v_generation_4960_, v_p_4961_, v_isNeg_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
return v___x_4978_;
}
else
{
lean_object* v_arg_4979_; lean_object* v___x_4980_; uint8_t v___x_4981_; 
v_arg_4979_ = lean_ctor_get(v___x_4976_, 1);
lean_inc_ref(v_arg_4979_);
v___x_4980_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4976_);
v___x_4981_ = l_Lean_Expr_isApp(v___x_4980_);
if (v___x_4981_ == 0)
{
lean_object* v___x_4982_; 
lean_dec_ref(v___x_4980_);
lean_dec_ref(v_arg_4979_);
v___x_4982_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4959_, v_generation_4960_, v_p_4961_, v_isNeg_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
return v___x_4982_;
}
else
{
lean_object* v_arg_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
v_arg_4983_ = lean_ctor_get(v___x_4980_, 1);
lean_inc_ref(v_arg_4983_);
v___x_4984_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4980_);
v___x_4985_ = l_Lean_Expr_isApp(v___x_4984_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; 
lean_dec_ref(v___x_4984_);
lean_dec_ref(v_arg_4983_);
lean_dec_ref(v_arg_4979_);
v___x_4986_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4959_, v_generation_4960_, v_p_4961_, v_isNeg_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
return v___x_4986_;
}
else
{
lean_object* v_arg_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; uint8_t v___x_4990_; 
v_arg_4987_ = lean_ctor_get(v___x_4984_, 1);
lean_inc_ref(v_arg_4987_);
v___x_4988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4984_);
v___x_4989_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addEqStep_updateRoots_spec__2___redArg___closed__1));
v___x_4990_ = l_Lean_Expr_isConstOf(v___x_4988_, v___x_4989_);
if (v___x_4990_ == 0)
{
uint8_t v___x_4991_; 
lean_dec_ref(v_arg_4983_);
v___x_4991_ = l_Lean_Expr_isApp(v___x_4988_);
if (v___x_4991_ == 0)
{
lean_object* v___x_4992_; 
lean_dec_ref(v___x_4988_);
lean_dec_ref(v_arg_4987_);
lean_dec_ref(v_arg_4979_);
v___x_4992_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4959_, v_generation_4960_, v_p_4961_, v_isNeg_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
return v___x_4992_;
}
else
{
lean_object* v___x_4993_; lean_object* v___x_4994_; uint8_t v___x_4995_; 
v___x_4993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4988_);
v___x_4994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___closed__1));
v___x_4995_ = l_Lean_Expr_isConstOf(v___x_4993_, v___x_4994_);
lean_dec_ref(v___x_4993_);
if (v___x_4995_ == 0)
{
lean_object* v___x_4996_; 
lean_dec_ref(v_arg_4987_);
lean_dec_ref(v_arg_4979_);
v___x_4996_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4959_, v_generation_4960_, v_p_4961_, v_isNeg_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
return v___x_4996_;
}
else
{
lean_object* v___x_4997_; 
v___x_4997_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4959_, v_generation_4960_, v_p_4961_, v_arg_4987_, v_arg_4979_, v_isNeg_4962_, v___x_4995_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
return v___x_4997_;
}
}
}
else
{
uint8_t v___x_4998_; 
lean_dec_ref(v___x_4988_);
v___x_4998_ = l_Lean_Expr_isProp(v_arg_4987_);
lean_dec_ref(v_arg_4987_);
if (v___x_4998_ == 0)
{
lean_object* v___x_4999_; 
v___x_4999_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goEq(v_proof_4959_, v_generation_4960_, v_p_4961_, v_arg_4983_, v_arg_4979_, v_isNeg_4962_, v___x_4998_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
return v___x_4999_;
}
else
{
lean_object* v___x_5000_; 
lean_dec_ref(v_arg_4983_);
lean_dec_ref(v_arg_4979_);
v___x_5000_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_goFact(v_proof_4959_, v_generation_4960_, v_p_4961_, v_isNeg_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
return v___x_5000_;
}
}
}
}
}
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5008_; 
lean_dec_ref(v_p_4961_);
lean_dec(v_generation_4960_);
lean_dec_ref(v_proof_4959_);
v_a_5001_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5003_ = v___x_4974_;
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_4974_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5006_; 
if (v_isShared_5004_ == 0)
{
v___x_5006_ = v___x_5003_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go___boxed(lean_object* v_proof_5009_, lean_object* v_generation_5010_, lean_object* v_p_5011_, lean_object* v_isNeg_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_){
_start:
{
uint8_t v_isNeg_boxed_5024_; lean_object* v_res_5025_; 
v_isNeg_boxed_5024_ = lean_unbox(v_isNeg_5012_);
v_res_5025_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5009_, v_generation_5010_, v_p_5011_, v_isNeg_boxed_5024_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_);
lean_dec(v_a_5022_);
lean_dec_ref(v_a_5021_);
lean_dec(v_a_5020_);
lean_dec_ref(v_a_5019_);
lean_dec(v_a_5018_);
lean_dec_ref(v_a_5017_);
lean_dec(v_a_5016_);
lean_dec_ref(v_a_5015_);
lean_dec(v_a_5014_);
lean_dec(v_a_5013_);
return v_res_5025_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4(void){
_start:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5034_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__2___redArg___closed__5));
v___x_5035_ = l_Lean_Name_append(v___x_5034_, v___x_5033_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep(lean_object* v_fact_5036_, lean_object* v_proof_5037_, lean_object* v_generation_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_){
_start:
{
lean_object* v___y_5051_; lean_object* v___y_5052_; lean_object* v___y_5053_; lean_object* v___y_5054_; lean_object* v___y_5055_; lean_object* v___y_5056_; lean_object* v___y_5057_; lean_object* v___y_5058_; lean_object* v___y_5059_; lean_object* v___y_5060_; lean_object* v___y_5064_; lean_object* v___y_5065_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v___x_5081_; lean_object* v_options_5082_; uint8_t v_hasTrace_5083_; 
lean_inc_ref(v_fact_5036_);
v___x_5081_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_storeFact___redArg(v_fact_5036_, v_a_5039_);
lean_dec_ref(v___x_5081_);
v_options_5082_ = lean_ctor_get(v_a_5047_, 2);
v_hasTrace_5083_ = lean_ctor_get_uint8(v_options_5082_, sizeof(void*)*1);
if (v_hasTrace_5083_ == 0)
{
v___y_5064_ = v_a_5039_;
v___y_5065_ = v_a_5040_;
v___y_5066_ = v_a_5041_;
v___y_5067_ = v_a_5042_;
v___y_5068_ = v_a_5043_;
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
v___y_5072_ = v_a_5047_;
v___y_5073_ = v_a_5048_;
goto v___jp_5063_;
}
else
{
lean_object* v_inheritedTraceOptions_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; uint8_t v___x_5087_; 
v_inheritedTraceOptions_5084_ = lean_ctor_get(v_a_5047_, 13);
v___x_5085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__3));
v___x_5086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4, &l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__4);
v___x_5087_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5084_, v_options_5082_, v___x_5086_);
if (v___x_5087_ == 0)
{
v___y_5064_ = v_a_5039_;
v___y_5065_ = v_a_5040_;
v___y_5066_ = v_a_5041_;
v___y_5067_ = v_a_5042_;
v___y_5068_ = v_a_5043_;
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
v___y_5072_ = v_a_5047_;
v___y_5073_ = v_a_5048_;
goto v___jp_5063_;
}
else
{
lean_object* v___x_5088_; 
v___x_5088_ = l_Lean_Meta_Grind_updateLastTag(v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v___x_5089_; lean_object* v___x_5090_; 
lean_dec_ref_known(v___x_5088_, 1);
lean_inc_ref(v_fact_5036_);
v___x_5089_ = l_Lean_MessageData_ofExpr(v_fact_5036_);
v___x_5090_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_removeParents_spec__1___redArg(v___x_5085_, v___x_5089_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_dec_ref_known(v___x_5090_, 1);
v___y_5064_ = v_a_5039_;
v___y_5065_ = v_a_5040_;
v___y_5066_ = v_a_5041_;
v___y_5067_ = v_a_5042_;
v___y_5068_ = v_a_5043_;
v___y_5069_ = v_a_5044_;
v___y_5070_ = v_a_5045_;
v___y_5071_ = v_a_5046_;
v___y_5072_ = v_a_5047_;
v___y_5073_ = v_a_5048_;
goto v___jp_5063_;
}
else
{
lean_dec(v_generation_5038_);
lean_dec_ref(v_proof_5037_);
lean_dec_ref(v_fact_5036_);
return v___x_5090_;
}
}
else
{
lean_dec(v_generation_5038_);
lean_dec_ref(v_proof_5037_);
lean_dec_ref(v_fact_5036_);
return v___x_5088_;
}
}
}
v___jp_5050_:
{
uint8_t v___x_5061_; lean_object* v___x_5062_; 
v___x_5061_ = 0;
v___x_5062_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5037_, v_generation_5038_, v_fact_5036_, v___x_5061_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
return v___x_5062_;
}
v___jp_5063_:
{
lean_object* v___x_5074_; uint8_t v___x_5075_; 
lean_inc_ref(v_fact_5036_);
v___x_5074_ = l_Lean_Expr_cleanupAnnotations(v_fact_5036_);
v___x_5075_ = l_Lean_Expr_isApp(v___x_5074_);
if (v___x_5075_ == 0)
{
lean_dec_ref(v___x_5074_);
v___y_5051_ = v___y_5064_;
v___y_5052_ = v___y_5065_;
v___y_5053_ = v___y_5066_;
v___y_5054_ = v___y_5067_;
v___y_5055_ = v___y_5068_;
v___y_5056_ = v___y_5069_;
v___y_5057_ = v___y_5070_;
v___y_5058_ = v___y_5071_;
v___y_5059_ = v___y_5072_;
v___y_5060_ = v___y_5073_;
goto v___jp_5050_;
}
else
{
lean_object* v_arg_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; uint8_t v___x_5079_; 
v_arg_5076_ = lean_ctor_get(v___x_5074_, 1);
lean_inc_ref(v_arg_5076_);
v___x_5077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5074_);
v___x_5078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep___closed__1));
v___x_5079_ = l_Lean_Expr_isConstOf(v___x_5077_, v___x_5078_);
lean_dec_ref(v___x_5077_);
if (v___x_5079_ == 0)
{
lean_dec_ref(v_arg_5076_);
v___y_5051_ = v___y_5064_;
v___y_5052_ = v___y_5065_;
v___y_5053_ = v___y_5066_;
v___y_5054_ = v___y_5067_;
v___y_5055_ = v___y_5068_;
v___y_5056_ = v___y_5069_;
v___y_5057_ = v___y_5070_;
v___y_5058_ = v___y_5071_;
v___y_5059_ = v___y_5072_;
v___y_5060_ = v___y_5073_;
goto v___jp_5050_;
}
else
{
lean_object* v___x_5080_; 
lean_dec_ref(v_fact_5036_);
v___x_5080_ = l___private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_addFactStep_go(v_proof_5037_, v_generation_5038_, v_arg_5076_, v___x_5079_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
return v___x_5080_;
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
lean_object* v___x_5228_; 
v___x_5228_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Core_0__Lean_Meta_Grind_processNewFactsImpl_spec__0___redArg(v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
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
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v_a_5229_; lean_object* v___x_5231_; uint8_t v_isShared_5232_; uint8_t v_isSharedCheck_5242_; 
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5231_ = v___x_5228_;
v_isShared_5232_ = v_isSharedCheck_5242_;
goto v_resetjp_5230_;
}
else
{
lean_inc(v_a_5229_);
lean_dec(v___x_5228_);
v___x_5231_ = lean_box(0);
v_isShared_5232_ = v_isSharedCheck_5242_;
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
lean_object* v___x_5234_; lean_object* v___x_5236_; 
v___x_5234_ = lean_box(0);
if (v_isShared_5232_ == 0)
{
lean_ctor_set(v___x_5231_, 0, v___x_5234_);
v___x_5236_ = v___x_5231_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5234_);
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
v_val_5238_ = lean_ctor_get(v_fst_5233_, 0);
lean_inc(v_val_5238_);
lean_dec_ref_known(v_fst_5233_, 1);
if (v_isShared_5232_ == 0)
{
lean_ctor_set(v___x_5231_, 0, v_val_5238_);
v___x_5240_ = v___x_5231_;
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
v_a_5243_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5228_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5228_);
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
